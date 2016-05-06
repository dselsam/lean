import logic

set_option blast.strategy "simple"
set_option blast.ematch true

universes l₁ l₂
constants (A : Type.{l₁}) (B : A → A → Type.{l₂}) (f : Π a₁ a₂, B a₁ a₂)
          (f_comm : ∀ a₁ a₂, f a₁ a₂ == f a₂ a₁)
attribute f_comm [forward]

definition lam1 : (λ (x y : A), f x y) == (λ (x y : A), f y x) := by blast
print lam1


/-
definition lam2 : (λ (x : A) (z w : A'), f (g z x) w) == (λ x z w, g w (f x z)) := by blast
definition lam3 : (λ (x y : A) (z w : A'), f (g z x) w) == (λ (x y : A) (z w : A'), g w (f x z)) := by blast
-/
