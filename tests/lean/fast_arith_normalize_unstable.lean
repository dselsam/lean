import algebra.ring algebra.arith_util

constants (A : Type.{1}) (A_inst : linear_ordered_field A) (u v w x y z : A)
attribute [instance] A_inst

-- fast_cancel_monomials
print "--------------"
set_option arith_normalizer.orient_polys false
#fast_arith_normalize 2 * x = x
#fast_arith_normalize x = 2 * x
#fast_arith_normalize 2 * x = 3 * x
#fast_arith_normalize 3 * x = 2 * x

print "--------------"
set_option arith_normalizer.orient_polys false
#fast_arith_normalize 1 = x
#fast_arith_normalize x = y + x
#fast_arith_normalize x = x + y
#fast_arith_normalize 1 + x = x
#fast_arith_normalize 0 = x + y
#fast_arith_normalize 1 = x + y

namespace test_nat
constants (m n : ℕ)
set_option arith_normalizer.orient_polys true
#fast_arith_normalize 0 = n + m
end test_nat
