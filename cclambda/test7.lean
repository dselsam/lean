import logic algebra.ring_bigops data.list

set_option blast.strategy "simple"
set_option blast.ematch true

constants (A : Type.{1}) (A_ring : ring A)
attribute A_ring [instance]
attribute mul_one [forward]
attribute zero_add [forward]

definition test1 (xs : list A) : (∑ x ← xs, x * 1) = (∑ x ← xs, x) := by blast
definition test2 (xs : list A) : (∑ x ← xs, 0 + (x * 1 * x)) = (∑ x ← xs, x * x) := by blast
