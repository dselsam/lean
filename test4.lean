prelude
import .mathlib4
namespace test
--example (R A : Type) [field R] : has_scalar R A := inferInstance
example (R A : Type) [field R] [ring A] [algebra R A] : has_scalar R A := inferInstance
axiom R : Type
axiom A : Type
@[instance] axiom fR : field R
#synth has_scalar R A
@[instance] axiom rA : ring A
@[instance] axiom alRA : algebra R A
#synth has_scalar R A
namespace test2
axiom R : Type
axiom A : Type
@[instance] axiom fR : discrete_linear_ordered_field R
#synth has_scalar R A
@[instance] axiom rA : ring A
@[instance] axiom alRA : algebra R A
#synth has_scalar R A
end test2
end test
