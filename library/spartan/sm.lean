namespace monad
namespace state

inductive Result (S : Type) (A : Type) :=
| success    : A → S → Result S A
| failure {} : Result S A

definition State (S A : Type) := S → Result S A

definition fmap {S A B : Type} (f : A → B) (Prog : State S A) : State S B :=
λ s, match Prog s with
     | (Result.success a s') := Result.success (f a) s'
     | Result.failure := Result.failure
     end

definition ret {S A : Type} (a : A) : State S A := λ s, Result.success a s

definition bind {S A B : Type} (Prog₁ : State S A) (Prog₂ : A → State S B) : State S B :=
λ s₁, match Prog₁ s₁ with
      | (Result.success a s₂) := Prog₂ a s₂
      | Result.failure := Result.failure
      end

definition is_monad [instance] {S : Type} : monad (State S) :=
monad.mk (@fmap S) (@ret S) (@bind S)

definition fail {S A : Type} : State S A := λ s, Result.failure
definition guard {S : Type} (P : S → Prop) [decidable_pred P] : State S unit :=
λ s, if P s then Result.success unit.star s else Result.failure

definition get {S : Type} : State S S := λ (s : S), Result.success s s
definition gets {S X : Type} (f : S → X) : State S X := state.bind get (λ s, return (f s))

definition put {S : Type} (s_new : S) : State S unit := λ (s : S), Result.success unit.star s_new

definition modify {S : Type} (f : S → S) : State S unit := state.bind get (λ s', put (f s'))

definition run_state {S A : Type} (Prog : State S A) (s : S) : option (prod A S) :=
  match Prog s with
  | (Result.success a s') := some (a, s')
  | Reult.failure := none
  end

definition eval_state {S A : Type} (Prog : State S A) (s : S) : option A :=
  match Prog s with
  | (Result.success a s') := some a
  | Reult.failure := none
  end

definition exec_state {S A : Type} (Prog : State S A) (s : S) : option S :=
  match Prog s with
  | (Result.success a s') := some s'
  | Reult.failure := none
  end

definition sequence {S : Type} : list (State S unit) → State S unit
| (list.cons prog progs) := bind prog (λ ignore, sequence progs)
| list.nil := return unit.star

end state
end monad
open monad.state

/-
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
have H₁ : HoareTriple (λ (s₁ : S), true ∧ (∀ a s₂, s₂ = s₁ ∧ a = s₁ → true))
                      (state.bind get (λ s', put (f s')))
                      (λ s₁ b s₃, ∃ a s₂, (s₂ = s₁ ∧ a = s₁) ∧ s₃ = (f s₁)), from bind_SPEC get (λ s', put (f s')) get_SPEC (λ a, put_SPEC (f a)),
have H₂ : HoareTriple (λ (s₁ : S), true)
                      (state.bind get (λ s', put (f s')))
                      (λ s₁ b s₃, ∃ a s₂, (s₂ = s₁ ∧ a = s₁) ∧ s₃ = (f s₁)),
     from strengthen_PRE H₁ (λ s ig₁, and.intro trivial (λ ig₁ ig₂ ig₃, trivial)),
have H₃ : HoareTriple (λ (s₁ : S), true)
                      (state.bind get (λ s', put (f s')))
                      (λ s₁ b s₃, s₃ = f s₁),
     from weaken_POST H₂ (λ s ig₁ s' ex₁,
                         Exists.cases_on ex₁
                           (λ a₁ ex₂, Exists.cases_on ex₂ (λ a₂ and₁, and.elim_right and₁))),
H₃

-- The overall strategy would be: see what PRE and POST the bind version would yield, and then strengthen and weaken.
end hoare
-/
