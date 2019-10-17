import .mathlib
noncomputable theory
namespace test
example (R A : Type) [field R] : has_scalar R A := infer_instance
example (R A : Type) [field R] [ring A] [algebra R A] : has_scalar R A := infer_instance
--example (R A : Type) [discrete_linear_ordered_field R] : has_scalar R A := infer_instance
end test
