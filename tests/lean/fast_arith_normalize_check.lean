import algebra.ring algebra.arith_util
constants (A : Type.{1}) (A_inst : linear_ordered_field A) (u v w x y z : A)
attribute [instance] A_inst

-- coercions
print "--------------"
namespace coe
constants (x1 x2 : real) (q1 q2 : rat) (z1 z2 : int) (n1 n2 : nat)
set_option arith_normalizer.distribute_mul true
#fast_arith_normalize real.of_rat (1 : rat) = 1
#fast_arith_normalize 1 + (1 : rat) = 0
#fast_arith_normalize real.of_rat (1 : rat) + 1 = 2
#fast_arith_normalize real.of_rat (1 + 1) + 1 = 3
#fast_arith_normalize rat.of_int (1 + 1) + 1 = 3

#fast_arith_normalize 1 + real.of_rat (1 + rat.of_int 1) = 3
#fast_arith_normalize 2 + real.of_rat (3 + rat.of_int 5) = 10
#fast_arith_normalize 2 + real.of_rat (3 * rat.of_int 5) = 17
#fast_arith_normalize 2 + real.of_rat (3 * rat.of_int (5 + 1)) = 20
#fast_arith_normalize 2 + real.of_rat (3 * rat.of_int (5 + 1) + 2) = 22

#fast_arith_normalize 1 + real.of_rat (1 + rat.of_int (1 + int.of_nat n1) * 2) + 2
#fast_arith_normalize 1 + real.of_rat (1 + rat.of_int (1 + int.of_nat n1) * 2) + 2
#fast_arith_normalize 2 * real.of_rat (1 + rat.of_int (1 * int.of_nat n1 + 3) * 2) + 2
end coe

-- relations
print "--------------"
#fast_arith_normalize x > y -- ¬ (x ≤ y)
#fast_arith_normalize x ≥ y -- y ≤ x
#fast_arith_normalize x < y -- ¬ (y ≤ x)
#fast_arith_normalize x ≤ y -- x ≤ y
#fast_arith_normalize x = y -- x = y
