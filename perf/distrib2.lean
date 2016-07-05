import algebra.ordered_field
open tactic
-- Case 1: abstract ring

open simplifier.ac simplifier.unit simplifier.distrib
namespace ring_perf

constants (A : Type.{1}) [A_cr : discrete_linear_ordered_field A]
constants (x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ z₃ : A)
attribute A_cr [instance]

set_option simplify.max_steps 10000
set_option defeq_canonicalize.shrink_add_weight 10
set_option defeq_canonicalize.shrink_mul_weight 0.1

lemma foo21 : (x₁ + y₁) = (y₁ + x₁) := by simp >> triv
lemma foo22 : (x₁ + y₁) * (x₂ + y₂) = (y₂ + x₂) * (y₁ + x₁) := by simp >> triv
lemma foo23 : (x₁ + y₁) * (x₂ + y₂) * (x₃ + y₃) = (y₃ + x₃) * (y₂ + x₂) * (y₁ + x₁) := by simp >> triv
lemma foo32 : (x₁ + y₁ + z₁) * (x₂ + y₂ + z₂) = (z₂ + y₂ + x₂) * (z₁ + y₁ + x₁) := by simp >> triv
lemma foo33 : (x₁ + y₁ + z₁) * (x₂ + y₂ + z₂) * (x₃ + y₃ + z₃) = (z₃ + y₃ + x₃) * (z₂ + y₂ + x₂) * (z₁ + y₁ + x₁) := by simp >> triv

end ring_perf
