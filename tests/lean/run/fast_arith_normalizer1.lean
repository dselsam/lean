import algebra.ordered_field algebra.module

namespace tactic
meta_constant fast_arith_normalize : expr → tactic (prod expr expr)

meta_definition fast_arith : tactic unit :=
do (new_target, Heq) ← target >>= fast_arith_normalize,
   assert "Htarget" new_target,
   reflexivity,
   Ht       ← get_local "Htarget",
   mk_app ("eq" <.> "mpr") [Heq, Ht] >>= exact

end tactic
open tactic

namespace test_ring

constants (A : Type.{1}) (A_inst : ring A) (x y z w : A)
attribute [instance] A_inst

-- basic AC over addition
example : y + x = x + y := by fast_arith
example : w + y + x + z = x + y + z + w := by fast_arith

-- Basic fusion on one variable
example : x = x := by fast_arith
example : 1 * x = x := by fast_arith
example : x + x = 2 * x := by fast_arith
example : x + x + x = 3 * x := by fast_arith
example : 2 * x + x + x = 4 * x := by fast_arith
example : 2 * x + 1 * x + x = 4 * x := by fast_arith
example : 2 * x + 1 * x + 1 * x = 4 * x := by fast_arith
example : x + 4 * x + x = 6 * x := by fast_arith

-- Basic fusion on two variables
example : y + x = x + y := by fast_arith
example : y + 1 * x = x + y := by fast_arith
example : x + y + x = 2 * x + y := by fast_arith
example : x + x + 1 * y + x = 3 * x + y := by fast_arith
example : 2 * x + 2 * y + x + 3 * y + x = 4 * x + 5 * y := by fast_arith
example : 2 * x + 3 * y + 1 * x + x + y = 4 * x + 4 * y := by fast_arith
example : y + y + 2 * y + 2 * x + 1 * x + 1 * x + y = 4 * x + 5 * y := by fast_arith
example : x + y + 4 * x + x = 6 * x + y := by fast_arith

-- Fusion on one variable with negative coefficients
example : - x = (-1) * x := by fast_arith
example : - x + - x = (-2) * x := by fast_arith
example : - x + x = 0 := by fast_arith
example : x + (- x) = 0 := by fast_arith
example : 1 * x + (- 1) * x = 0 := by fast_arith
example : 2 * x + (- 2) * x = 0 := by fast_arith
example : 1 * x + (- 2) * x + x = 0 := by fast_arith
example : (-3) * x + 4 * x + (-2) * x + x = 0 by fast_arith

-- One variable with unary minuses
example : 2 * x + 2 * (- x) = 0 := by fast_arith
example : 3 * -x + 4 * x - x = 0 := by fast_arith

-- Fusion on two variables with negative coefficients
example : y + -x = -x + y := by fast_arith
example : y + (-1) * x = -x + y := by fast_arith
example : x + - y + - x = - y := by fast_arith
example : x + - x + 1 * y + x = x + y := by fast_arith
example : 2 * x + (- 2) * y + x + 3 * y + x = 4 * x + y := by fast_arith
example : (- 2) * x + 3 * y + 1 * x + x + y = 4 * y := by fast_arith
example : y + - y + 2 * y + 2 * x + 1 * x + (- 1) * x + y = 2 * x + 3 * y := by fast_arith
example : x + y + (- 4) * x + - x = (- 4) * x + y := by fast_arith

end test_ring

namespace test_comm_ring

constants (A : Type.{1}) (A_inst : comm_ring A) (x y z w : A)
attribute [instance] A_inst

-- basic AC over multiplication
example : y * x = x * y := by fast_arith
example : w * y * x * z = x * y * z * w := by fast_arith

set_option arith_normalizer.som true

-- basic distrib
example : x * (y + z) = x * y + x * z := by fast_arith
example : (y + z) * x = x * y + x * z := by fast_arith
example : (y + z) * (x + w) = x * y + x * z + (w * y) + (w * z) := by fast_arith
example : (y + z) * (x + w) * (x + w) = x * x * y + x * w * y + w * x * y + w * w * y + x * x * z + x * w * z + w * x * z + w * w * z := by fast_arith

end test_comm_ring

namespace test_field

constants (A : Type.{1}) (A_inst : field A) (x y z w : A)
attribute [instance] A_inst

-- Basic simplification with division
example : x * (y / z) = (x * y) / z := by fast_arith
example : (3 / (y * z)) / 4 = (3 / 4) * (1 / (y * z)) := by fast_arith -- TODO(dhs)
example : (x / y) / x = x / (x * y) := by fast_arith
example : (x / (- y)) / (- 2 * x) = (1 / 2) * (1 / y) := by fast_arith

end test_field

namespace test_module

constants (A R : Type.{1}) (R_inst : ring R) (a b c d : R)
attribute [instance] R_inst
constants (A_inst : left_module R A) (u v w x y z : A)
attribute [instance] A_inst

-- Basic scalar collection
example : a • (b • u) = (a * b) • u := by fast_arith
example : a • (b • (u + v)) = (a * b) • u + (a * b) • v := by fast_arith
example : a • (u + v) = a • u + a • v := by fast_arith
example : a • (u + v + w) = a • u + a • v + a • w := by fast_arith
example : a • (u + (b • v) + w) = a • u + (a * b) • v + a • w := by fast_arith
example : (a * (c + d)) • (u + (b • v) + w) = (a * c + a * d) • u + (a * b * c + a * b * d) • v + (a * c + a * d) • w := by fast_arith

end test_module
