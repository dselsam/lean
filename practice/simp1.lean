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

--example : (a ∧ d) = (b ∧ d ∧ c) := by simp

constants (f : Prop → Prop) (Hf : ∀ x, f x = x)

meta_definition simp_fx_to_x : tactic unit := mk_eq_simp_ext $
  λ e, do pf ← mk_app `Hf [expr.app_arg e],
          return (expr.app_arg e, pf)

register_simp_ext f simp_fx_to_x

example : (f a ∧ d) = (b ∧ d ∧ c) := by simp
