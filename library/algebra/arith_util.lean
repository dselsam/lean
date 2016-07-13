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

--attribute real.of_rat [coercion]
--attribute rat.of_int [coercion]
--attribute int.of_nat [coercion]

-- TODO(dhs): this may not be the best way to do this
structure cyclic_numerals [class] (A : Type) [comm_ring A] := (a₀ : A)  (cyclic : ∀ a k : A , a = a - k * a₀)

constant (bv : nat → Type.{1})
constant (bv_cr : ∀ n, field (bv n))
attribute bv_cr [instance]
constant (bv_cn : ∀ n, cyclic_numerals (bv n))
attribute bv_cn [instance]
