import algebra.binary
open tactic

constants (a b c d e : Prop)
constants (H : a = (b ∧ c))

constants (and_assoc : is_associative and) (or_assoc : is_associative or)
attribute and_assoc [instance]
attribute or_assoc [instance]

attribute H [simp]
set_option trace.app_builder true
set_option trace.simplifier true
--set_option trace.debug.simplifier.try_rewrite true

print congr_arg_bin_fst

print is_associative.op_assoc

example : (a ∧ d) = (b ∧ d ∧ c) := by simp
