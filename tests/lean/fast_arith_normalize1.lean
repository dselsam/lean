import algebra.ring algebra.arith_util

constants (A : Type.{1}) (A_inst : field A) (u v w x y z : A)
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
#fast_arith_normalize (x + y) * 2 * (z + w) * 3 = 5*x*z + 5*y*z + 5*x*w + 5*y*w
#fast_arith_normalize (x + y) * 3 * (y + z) * 2 = 6 * x * y + 6 * x * z + 6 * y * y + 6 * y * z
#fast_arith_normalize (x + v) * (y + z) * (w + (y * (z + u))) = (w + (y * (z + u))) * (z + y) * (v + x)
#fast_arith_normalize (x * (y + (x * (y + (x * (y + x)))))) = x * y + x * x * y + x * x * x * y + x * x * x * x
set_option arith_normalizer.distribute_mul false

-- neg
print "--------------"
set_option arith_normalizer.distribute_mul true
#fast_arith_normalize - x = -1 * x
#fast_arith_normalize - (5 * x) = (-5) * x
#fast_arith_normalize - (-5 * x) = 5 * x
#fast_arith_normalize - - x = x
#fast_arith_normalize - - - x = - x

#fast_arith_normalize x + - x
#fast_arith_normalize x + - x + (-4) * x + 4 * (-x) + 8 * x
#fast_arith_normalize x + - x + (-4) * x + 4 * (-x) + 8 * x
#fast_arith_normalize x * (-y) + (-x) * y + (-x) * (-y) * x * y

#fast_arith_normalize x + y + -x + -y
#fast_arith_normalize -(x * y) = x * -y
#fast_arith_normalize -(x * -y) = x * y
#fast_arith_normalize -(x * -(y + z)) = x * y + -x*z
#fast_arith_normalize x * (-y) + (-x) * y + (-x) * (-y) + x * y
set_option arith_normalizer.distribute_mul false

-- sub
print "--------------"
set_option arith_normalizer.distribute_mul true
#fast_arith_normalize x - y = 2 * x - (- (-1) * y) - x
#fast_arith_normalize -(x + (y - x)) = 2 * y - 3 * y
#fast_arith_normalize x - (y - x) = x - y + x
#fast_arith_normalize x * (- x) * (- y) * y = x * x * y * y
#fast_arith_normalize x + (x - y) + y - x - x = 0
#fast_arith_normalize x + -(x - y) - y = 0
set_option arith_normalizer.distribute_mul false

-- div
print "--------------"
set_option arith_normalizer.distribute_mul true
#fast_arith_normalize (1:A) / 1 - 1
#fast_arith_normalize (2:A) / 1 - 2
#fast_arith_normalize (2:A) / 2 - 1
#fast_arith_normalize (1:A) / 2 - (1/2)

#fast_arith_normalize x / y - (2 * x) / (2 * y)
#fast_arith_normalize x / 1 - x
#fast_arith_normalize x / 2 - (1/2) * x
#fast_arith_normalize x / (3 / 2) - (2/3) * x

#fast_arith_normalize x / 0 = div0 x
#fast_arith_normalize (5 * y) / y = y / ((1/5) * y)
#fast_arith_normalize (5 * y) / (5 * y) = y / y

#fast_arith_normalize y / (2 * x) - (1/2) * (y / x)
set_option arith_normalizer.distribute_mul false

-- coercions
print "--------------"
set_option trace.app_builder true
check real.of_rat
check (1 : rat)
#fast_arith_normalize real.of_rat (1 : rat)
