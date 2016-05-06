import logic

set_option blast.strategy "simple"
set_option blast.ematch true

universes l₁ l₂
constants (B : Type.{l₂})
          (φ₁ φ₂ : Π {C : Type}, C → B)
          (op : B → B → B)
          (op.comm : ∀ x y, op x y = op y x)
attribute op.comm [forward]

set_option trace.cc.lambda true
definition lam1 {A A' : Type.{l₁}} (H : A = A') : (λ (a : A), op (φ₁ a) (φ₂ a)) == (λ (a' : A'), op (φ₁ a') (φ₂ a')) := by blast

--definition lam2 (H : A = A') : (λ (a : A), op (φ₁ a) (φ₂ a)) == (λ (a' : A'), op (φ₂ a') (φ₁ a')) := by blast


/-

xs ys : finset var,
φ₁ : factor xs,
φ₂ : factor ys
⊢ (λ (γ : assignment (xs ∪ ys)), φ₁ (restrict γ xs sorry) * φ₂ (restrict γ ys sorry)) == λ
  (γ : assignment (ys ∪ xs)),
    φ₂ (restrict γ ys sorry) * φ₁ (restrict γ xs sorry)
-/
