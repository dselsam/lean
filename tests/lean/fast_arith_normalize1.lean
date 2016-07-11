import algebra.ring

constants (A : Type.{1}) (A_inst : comm_ring A) (x y z w : A)
attribute [instance] A_inst

-- fast_normalize_add
print "--------------"
#fast_arith_normalize x + y
#fast_arith_normalize x + y + z
#fast_arith_normalize x + y + z + w

#fast_arith_normalize x + x
#fast_arith_normalize x + x + x

#fast_arith_normalize x + y + x + y
#fast_arith_normalize x + y + x + y + x + y

#fast_arith_normalize x + y + x + y + 1
#fast_arith_normalize 1 + x + y + x + y + 1

#fast_arith_normalize 0 + 0 * x + x + y + (-1) * x + y + 1
#fast_arith_normalize 0 + 0 * x + x + y + (-1) * x + (-1) * y + 1
#fast_arith_normalize 0 + 0 * x + x + y + (-1) * x + (-1) * y + 1 + (-1)

#fast_arith_normalize 1 + 2 + 3 + x + 2 * x + 1

-- fast_cancel_monomials
print "--------------"
set_option arith_normalizer.orient_polys false
#fast_arith_normalize x = x
#fast_arith_normalize x + y = x + y
#fast_arith_normalize x + y = y + x
#fast_arith_normalize 2 * x + y = y + 2 * x
#fast_arith_normalize 2 * x + 3 * y = 3 * y + 2 * x

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

print "--------------"
set_option arith_normalizer.orient_polys true
#fast_arith_normalize 0 = x + y
#fast_arith_normalize 1 = x + y
#fast_arith_normalize 0 = x + y + z
#fast_arith_normalize -1 = (-1) * x + (-1) * y + (-1) * z

print "--------------"
--set_option trace.arith_normalizer.fast.normalize_mul true
#fast_arith_normalize x * y = y * x
#fast_arith_normalize x * y * x = y * x * x
#fast_arith_normalize x * y * x = x * x * y

print "--------------"
#fast_arith_normalize 2 * x * y * x * 4 = 8 * (x * (x * y))
#fast_arith_normalize 2 * x * y * 3 = 6 * (x * y)

print "--------------"
set_option arith_normalizer.distribute_mul false
#fast_arith_normalize 3 * x * (y + z) * 2 = 6 * x * (y + z)
#fast_arith_normalize (x + y) * 3 * (y + z) * 2 = 6 * (x + y) * (y + z)

print "--------------"
set_option arith_normalizer.distribute_mul true
#fast_arith_normalize 2 * (x + y) = 0
#fast_arith_normalize 2 * (x + y) = 2 * x + 2 * y
#fast_arith_normalize 3 * x * (y + z) * 2 = 6 * x * y + 6 * x * z
#fast_arith_normalize (x + y) * 3 * (y + z) * 2 = 6 * x * y + 6 * x * z + 6 * y * y + 6 * y * z
#fast_arith_normalize (x + w) * (y + z) * (w + (x * (z + w))) = (w + (x * (z + w))) * (w + x) * (z + y)
