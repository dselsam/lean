import logic

set_option pp.purify_locals false
set_option blast.strategy "cc"
set_option trace.app_builder true


namespace cclambda

namespace domain_types_equal


set_option pp.all true
---set_option trace.cc.state true
--set_option trace.cc.merge true
--set_option trace.cc.propagation true
--set_option trace.app_builder true
constants (A A' : Type.{1}) (B : A → Type.{1}) (B' : A' → Type.{1}) (f : Π a, B a) (f' : Π a', B' a')
--set_option trace.cc.lambda true

definition test1 : (A = A') → (λ a:A, a) == (λ a':A', a') := by blast


--set_option trace.cc.state true
--definition test2 : (A = A') → (B == B') → (λ (a : A) (b : B a), a) == (λ (a' : A') (b' : B' a'), a') := by blast

end domain_types_equal



/-
universes l₁ l₂
constants (A : Type.{l₁}) (B : A → A → Type.{l₂}) (f : Π a₁ a₂, B a₁ a₂) (a : A)

definition test1 : (λ a₀, f a₀ a) = (λ a₀, f a₀ a) := by inst_simp

constants (f₁ f₂ : Π a₁ a₂, B a₁ a₂) (Hf : f₁ = f₂)
attribute Hf [simp]

set_option trace.blast.ematch true


set_option trace.cc.propagation true

definition test2 : (∀ a₁ a₂, f₁ a₁ a₂ == f₂ a₁ a₂) → (λ a₀, f₁ a₀ a) = (λ a₀, f₂ a₀ a) := by inst_simp

print test1


-/
end cclambda
