prelude
import TypeClassPaper.mathlib4

namespace test

def synth_mul_action_example (k α β : Type)
    (_inst_1 : normed_field k)
    [_inst_2 : @mul_action k (α → β) (@ring.to_monoid k (@normed_ring.to_ring k (@normed_field.to_normed_ring k _inst_1)))]
  : Unit := ()

--set_option pp.all true
set_option trace.class_instances true

def try_synth_mul_action_example (k α β : Type) (_inst_1 : normed_field k) : Unit := synth_mul_action_example k α β _inst_1

end test
