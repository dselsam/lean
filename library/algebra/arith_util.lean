import algebra.ordered_field

definition div0 {A : Type} [field A] (x : A) : A := div x 0

constants (int rat real : Type.{1})
constants (int_locr : decidable_linear_ordered_comm_ring int)
constants (rat_lof : discrete_linear_ordered_field rat)
constants (real_lof : linear_ordered_field real)

attribute int_locr [instance]
attribute rat_lof [instance]
attribute real_lof [instance]

constants (real.of_rat : rat → real)
constants (rat.of_int : int → rat)
constants (int.of_nat : nat → int)

definition from_nat (A : Type) [has_zero A] [has_one A] [has_add A] : ℕ → A := sorry
structure cyclic_numerals [class] (A : Type) extends comm_ring A :=
(bound : ℕ)  (cyclic : ∀ a k : A , a = a - k * from_nat A bound)

constant (bv2 : Type.{1})
constant (bv2_cr : field bv2)
attribute bv2_cr [instance]
definition bv2_cn [instance] : cyclic_numerals bv2 := ⦃ cyclic_numerals bv2, bv2_cr, bound := 4, cyclic := sorry ⦄

print cyclic_numerals.bound
