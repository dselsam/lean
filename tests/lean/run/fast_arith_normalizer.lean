import algebra.ordered_field algebra.module

namespace tactic
meta_constant arith_normalize : expr → tactic (prod expr expr)

meta_definition arith : tactic unit :=
do (new_target, Heq) ← target >>= arith_normalize,
   assert "Htarget" new_target,
   triv,
   Ht       ← get_local "Htarget",
   mk_app ("eq" <.> "mpr") [Heq, Ht] >>= exact

end tactic
open tactic

namespace test_ring

constants (A : Type.{1}) (A_inst : discrete_linear_ordered_field A) (x y z w : A)
attribute [instance] A_inst

-- basic AC over addition
example : y + x = x + y := by arith
example : w + y + x + z = x + y + z + w := by arith

-- Basic fusion on one variable
example : x = x := by arith
example : 1 * x = x := by arith
example : x + x = 2 * x := by arith
example : x + x + x = 3 * x := by arith
example : 2 * x + x + x = 4 * x := by arith
example : 2 * x + 1 * x + x = 4 * x := by arith
example : 2 * x + 1 * x + 1 * x = 4 * x := by arith
example : x + 4 * x + x = 6 * x := by arith

-- Basic fusion on two variables
example : y + x = x + y := by arith
example : y + 1 * x = x + y := by arith
example : x + y + x = 2 * x + y := by arith
example : x + x + 1 * y + x = 3 * x + y := by arith
example : 2 * x + 2 * y + x + 3 * y + x = 4 * x + 5 * y := by arith
example : 2 * x + 3 * y + 1 * x + x + y = 4 * x + 4 * y := by arith
example : y + y + 2 * y + 2 * x + 1 * x + 1 * x + y = 4 * x + 5 * y := by arith
example : x + y + 4 * x + x = 6 * x + y := by arith

-- Fusion on one variable with negative coefficients
example : - x = (-1) * x := by arith
example : - x + - x = (-2) * x := by arith
example : - x + x = 0 := by arith
example : x + (- x) = 0 := by arith
example : 1 * x + (- 1) * x = 0 := by arith
example : 2 * x + (- 2) * x = 0 := by arith
example : 1 * x + (- 2) * x + x = 0 := by arith
example : (-3) * x + 4 * x + (-2) * x + x = 0 := by arith

-- One variable with unary minuses
example : 2 * x + 2 * (- x) = 0 := by arith
example : 3 * -x + 4 * x - x = 0 := by arith

-- Fusion on two variables with negative coefficients
example : y + -x = -x + y := by arith
example : y + (-1) * x = -x + y := by arith
example : x + - y + - x = - y := by arith
example : x + - x + 1 * y + x = x + y := by arith
example : 2 * x + (- 2) * y + x + 3 * y + x = 4 * x + y := by arith
example : (- 2) * x + 3 * y + 1 * x + x + y = 4 * y := by arith
example : y + - y + 2 * y + 2 * x + 1 * x + (- 1) * x + y = 2 * x + 3 * y := by arith
example : x + y + (- 4) * x + - x = (- 4) * x + y := by arith

end test_ring

namespace test_comm_ring

constants (A : Type.{1}) (A_inst : comm_ring A) (x y z w : A)
attribute [instance] A_inst

-- basic AC over multiplication
example : y * x = x * y := by arith
example : w * y * x * z = x * y * z * w := by arith
example : z * w * y * w * x * z = x * y * z * z * w * w:= by arith

set_option arith_normalizer.distribute_mul true

-- basic distrib
example : x * (y + z) = x * y + x * z := by arith
example : (y + z) * x = x * y + x * z := by arith
example : (y + z) * (x + w) = x * y + x * z + (w * y) + (w * z) := by arith
example : (y + z) * (x + w) * (x + w) = x * x * y + x * w * y + w * x * y + w * w * y + x * x * z + x * w * z + w * x * z + w * w * z := by arith

end test_comm_ring

namespace test_field

constants (A : Type.{1}) (A_inst : field A) (x y z w : A)
attribute [instance] A_inst

-- Basic simplification with division
example : (3 / (y * z)) / 4 = (1 / 4) * (3 / (y * z)) := by arith
example : (x / (- y)) / (- 2 * x) = (1 / 2) * ((x / y) / x) := by arith

end test_field
