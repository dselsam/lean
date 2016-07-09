import algebra.ordered_field algebra.module

namespace tactic
meta_constant arith_normalize : expr → tactic (prod expr expr)

meta_definition arith : tactic unit :=
do (new_target, Heq) ← target >>= arith_normalize,
   assert "Htarget" new_target,
   reflexivity,
   Ht       ← get_local "Htarget",
   mk_app ("eq" <.> "mpr") [Heq, Ht] >>= exact

end tactic
open tactic

--set_option trace.arith_normalizer.fast.cancel_monomials true
--set_option trace.type_context.is_def_eq_detail true
--set_option trace.class_instances true
namespace test_ring

constants (A : Type.{1}) (A_inst : comm_ring A) (x y z w : A)
attribute [instance] A_inst

--example : x = x := by arith


example : x + y = y + x := by arith
/-
example : x + y + z = z + y + x := by arith

example : 1 * x = 1 * x := by arith
example : 5 + 1 * x = 5 + 1 * x := by arith

example : 5 + 1 * x + 3 * y + 2 * y = 5 * y + 5 + 1 * x := by arith

example : x + x + x = 3 * x := by arith
example : x + x + 2 * x + 7 * y + x + y = 5 * x + 8 * y := by arith
-/
end test_ring
