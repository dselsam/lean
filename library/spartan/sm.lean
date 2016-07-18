namespace monad
namespace state

definition State (S A : Type) := S → prod A S
variable {S : Type}
namespace state

definition fmap : Π {A B : Type}, (A → B) → State S A → State S B :=
  λ (A B : Type) (f : A → B) (P : S → prod A S) (s : S),
     match P s with
     | (a, s') := (f a, s')
     end

definition ret : Π {A : Type}, A → State S A :=
  λ (A : Type) (a : A) (s : S), (a, s)

definition bind : Π {A B : Type}, State S A → (A → State S B) → State S B :=
  λ (A B : Type) (P₁ : State S A) (P₂ : A → State S B) (s₁ : S),
    match P₁ s₁ with
    | (a, s₂) := P₂ a s₂
    end
end state

definition is_monad [instance] : monad (State S) :=
monad.mk (@state.fmap S) (@state.ret S) (@state.bind S)

definition get : State S S := λ (s : S), (s, s)
definition put (s_new : S) : State S unit := λ (s : S), (unit.star, s_new)
definition modify (f : S → S) : State S unit := state.bind get (λ s', put (f s')) -- elaborator is nuts
definition run_state {A : Type} (P : State S A) (s : S) : prod A S := P s
definition eval_state {A : Type} (P : State S A) (s₁ : S) : A := match P s₁ with
                                                                | (a, s₂) := a
                                                                end

definition exec_state {A : Type} (P : State S A) (s₁ : S) : S := match P s₁ with
                                                                | (a, s₂) := s₂
                                                                end

end state
end monad
open monad.state

namespace hoare
variable {S : Type}

definition Pre := S → Prop
definition Post (A : Type) := S → A → S → Prop

definition HoareTriple {A : Type} (pre : Pre) (P : State S A) (post : Post A) :=
∀ s, pre s → match run_state P s with
               | (a, s') := post s a s'
               end
notation `⦃` P `⦄` S `⦃` Q `⦄` := HoareTriple P S Q

lemma strengthen_PRE {A : Type} {pre₁ pre₂ : Pre} {P : State S A} {post : Post A} :
  HoareTriple pre₁ P post → (∀ s, pre₂ s → pre₁ s) → HoareTriple pre₂ P post :=
assume H₁ : HoareTriple pre₁ P post,
assume H₂ : ∀ s, pre₂ s → pre₁ s,
assume (s : S) (p₂ : pre₂ s),
H₁ s (H₂ s p₂)

lemma weaken_POST {A : Type} {pre : Pre} {P : State S A} {post₁ post₂ : Post A} :
  HoareTriple pre P post₁ → (∀ s a s', post₁ s a s' → post₂ s a s') → HoareTriple pre P post₂ :=
assume H₁ : HoareTriple pre P post₁,
assume H₂ : ∀ {s} {a} {s'}, post₁ s a s' → post₂ s a s',
assume (s : S) (p : pre s),
@prod.cases_on _ _ (λ pair, match pair with (a, s') := post₁ s a s' end → match pair with (a, s') := post₂ s a s' end)
  (run_state P s)
  (λ a s', assume HP₁, H₂ HP₁)
  (H₁ s p)

lemma bind_SPEC {A B : Type} :
                ∀ (P₁ : State S A) (P₂ : A → State S B)
                {pre₁ : Pre} {pre₂ : A → Pre}
                {post₁ : Post A} {post₂ : A → Post B},
                HoareTriple pre₁ P₁ post₁ →
                (∀ a, HoareTriple (pre₂ a) (P₂ a) (post₂ a)) →
                HoareTriple (λ s₁, pre₁ s₁ ∧ (∀ a s₂, post₁ s₁ a s₂ → pre₂ a s₂))
                            (state.bind P₁ P₂)
                            (λ s₁ b s₃, ∃ a s₂, post₁ s₁ a s₂ ∧ post₂ a s₂ b s₃) := sorry

lemma get_SPEC : HoareTriple (λ (s : S), true) get (λ s a s', s' = s ∧ a = s) :=
assume (s : S) (ignore : true),
and.intro rfl rfl

lemma put_SPEC (s₀ : S) : HoareTriple (λ (s : S), true) (put s₀) (λ s a s', s' = s₀) :=
assume (s : S) (ignore : true),
rfl

lemma modify_SPEC (f : S → S) : HoareTriple (λ (s : S), true) (modify f) (λ s a s', s' = f s) :=
assume (s : S) (ignore : true),
rfl

lemma modify_SPEC_composition (f : S → S) : HoareTriple (λ (s : S), true) (state.bind get (λ s', put (f s'))) (λ s a s', s' = f s) :=
have H₁ : HoareTriple (λ (s : S), true) get (λ s a s', s' = s ∧ a = s), from get_SPEC,
have H₂ : ∀ (a : S), HoareTriple (λ (s : S), true) (put (f a)) (λ s b s', s' = f a), from assume a, put_SPEC (f a),
have H₃ : HoareTriple (λ (s₁ : S), true ∧ (∀ a s₂, s₂ = s₁ ∧ a = s₁ → true))
                      (state.bind get (λ s', put (f s')))
                      (λ s₁ b s₃, ∃ a s₂, (s₂ = s₁ ∧ a = s₁) ∧ s₃ = (f s₁)), from bind_SPEC get (λ s', put (f s')) H₁ H₂,
have H₄ : HoareTriple (λ (s₁ : S), true)
                      (state.bind get (λ s', put (f s')))
                      (λ s₁ b s₃, ∃ a s₂, (s₂ = s₁ ∧ a = s₁) ∧ s₃ = (f s₁)),
     from strengthen_PRE H₃ (λ s ig₁, and.intro trivial (λ ig₁ ig₂ ig₃, trivial)),
have H₅ : HoareTriple (λ (s₁ : S), true)
                      (state.bind get (λ s', put (f s')))
                      (λ s₁ b s₃, s₃ = f s₁),
     from weaken_POST H₄ (λ s ig₁ s' ex₁,
                         Exists.cases_on ex₁
                           (λ a₁ ex₂, Exists.cases_on ex₂ (λ a₂ and₁, and.elim_right and₁))),
H₅

-- The overall strategy would be: see what PRE and POST the bind version would yield, and then strengthen and weaken.
end hoare
