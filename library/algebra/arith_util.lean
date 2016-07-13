import algebra.ordered_field

definition div0 {A : Type} [field A] (x : A) : A := div x 0

constants (int rat real : Type.{1})
constants (int_locr : linear_ordered_comm_ring int)
constants (rat_lof : linear_ordered_field rat)
constants (real_lof : linear_ordered_field real)

attribute int_locr [instance]
attribute rat_lof [instance]
attribute real_lof [instance]

constants (real.of_rat : rat → real)
constants (rat.of_int : int → rat)
constants (int.of_nat : nat → int)

--attribute real.of_rat [coercion]
--attribute rat.of_int [coercion]
--attribute int.of_nat [coercion]
