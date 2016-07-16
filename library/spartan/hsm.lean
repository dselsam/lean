import data.list algebra.group
open subtype nat prod

structure HoareState (S : Type) (A : Type) :=
(pre    : S → Prop)
(post   : S → A → S → Prop)
(action : ∀ s : { s : S | pre s }, { as' : A × S | post (elt_of s) as'.1 as'.2 })

namespace HS

definition return {S : Type} {A : Type} (a : A) : HoareState S A :=
⦃ HoareState,
  pre    := λ s, true,
  post   := λ s a' s', s = s' ∧ a = a',
  action := λ (ss : { s : S | true }), tag (a, elt_of ss) sorry ⦄

definition bind {S A B : Type} (m₁ : HoareState S A) (m₂ : A → HoareState S B) : HoareState S B :=
⦃ HoareState,
  pre    := λ s₁, HoareState.pre m₁ s₁ ∧ (∀ a s₂, HoareState.post m₁ s₁ a s₂ → HoareState.pre (m₂ a) s₂),
  post   := λ s₁ b s₃, ∃ a s₂, HoareState.post m₁ s₁ a s₂ ∧ HoareState.post (m₂ a) s₂ b s₃,
  action := λ ss,
    match ss with
    | tag s₁ (and.intro p₁ p₂) := match HoareState.action m₁ (tag s₁ p₁) with
      | tag (a, s₂) p₃ := match HoareState.action (m₂ a) (tag s₂ (p₂ a s₂ p₃)) with
        | tag (b, s₃) p₄ := tag (b, s₃) (exists.intro a (exists.intro s₂ (and.intro p₃ (sorry))))
        end
      end
    end ⦄

end HS

namespace HS_defs
lemma return_post [simp] (a s a' s' : ℕ) : HoareState.post (HS.return a) s a' s' = (s = s' ∧ a = a') := rfl

definition get {S : Type} : HoareState S S :=
  HoareState.mk (λ s, true)
                (λ s a s', s = s' ∧ a = s)
                (λ ss : { s : S | true }, tag (elt_of ss, elt_of ss) sorry)

lemma get_post [simp] (s a s' : ℕ) : (HoareState.post get s a s') = (s = s' ∧ a = s) := rfl

definition put {S : Type} (s₀ : S) : HoareState S unit :=
  HoareState.mk (λ s, true)
                (λ s a s', s' = s₀)
                (λ ss : { s : S | true }, tag (unit.star, s₀) sorry)

lemma put_post [simp] (n s : ℕ) (a : unit) (s' : ℕ) : (HoareState.post (put n) s a s') = (s' = n) := rfl

definition modify {S : Type} (f : S → S) : HoareState S unit := HS.bind get (λ s, put (f s))

definition with_pre {S : Type} (pre : S → Prop) : HoareState S unit :=
  HoareState.mk pre (λ s a s', true) (λ ss, tag (unit.star, elt_of ss) sorry)

definition exec_state {S A : Type} (P : HoareState S A) (s₁ : S) (pre₁ : HoareState.pre P s₁) : S :=
  match HoareState.action P (tag s₁ pre₁) with
  | (tag (a, s₂) _) := s₂
  end

definition eval_state {S A : Type} (P : HoareState S A) (s₁ : S) (pre₁ : HoareState.pre P s₁) : A :=
  match HoareState.action P (tag s₁ pre₁) with
  | (tag (a, s₂) _) := a
  end

end HS_defs



----- Sample programs
/-
definition increment : HoareState ℕ unit := HS.bind get (λ n, put (succ n))

definition incrementN : ℕ → HoareState ℕ ℕ
| zero := get
| (succ n) := HS.bind increment (λ ignore, incrementN n)

definition ret_plus (n : ℕ) : HoareState ℕ ℕ := HS.bind get (λ (s:ℕ), HS.return (s + n))

lemma increment_correct : ∀ n s res s', HoareState.post (incrementN n) s res s' → s' = res ∧ res = s + n := sorry
lemma ret_plus_correct : ∀ (n s res s' : ℕ), HoareState.post (ret_plus n) s res s' → s' = s ∧ res = s + n := sorry

lemma inc_then_ret_plus_correct : ∀ (m n s res s' : ℕ),
  HoareState.post (HS.bind (incrementN m) (λ ignore, ret_plus n)) s res s' →
    s' = s + m ∧ res = s' + n := sorry


namespace relabel

inductive tree (A : Type) : Type :=
| leaf : A → tree A
| node : tree A → tree A → tree A

open tree list

definition size {A : Type} : tree A → ℕ
| (leaf a) := 1
| (node t1 t2) := size t1 + size t2

definition seq : ℕ → ℕ → list ℕ
| _ zero := []
| m (succ n) := cons m (seq (succ m) n)

definition flatten {A : Type} : tree A → list A
| (leaf a) := [a]
| (node t1 t2) := flatten t1 ++ flatten t2

definition relabel {A : Type} : tree A → HoareState ℕ (tree ℕ)
| (leaf _) := HS.bind get (λ n, HS.bind (put n) (λ ignore, HS.return (leaf n)))
| (node t₁ t₂) := HS.bind (relabel t₁) (λ u₁, HS.bind (relabel t₂) (λ u₂, HS.return (node u₁ u₂)))

lemma relabel_correct {A : Type} : Π (t : tree A) s ret s',
  HoareState.post (relabel t) s ret s' →
    (s' = s + size ret ∧ flatten ret = seq s (size ret))
| (leaf a) := sorry
| (node t₁ t₂) := sorry


end relabel
-/
