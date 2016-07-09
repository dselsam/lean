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

set_option trace.arith_normalizer.fast true
--set_option trace.type_context.is_def_eq_detail true
--set_option trace.class_instances true
namespace test_ring

constants (A : Type.{1}) (A_inst : comm_ring A) (x y z w : A)
attribute [instance] A_inst

example : x = x := by arith
example : x + y = y + x := by arith

end test_ring
