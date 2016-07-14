import algebra.ring algebra.arith_util

constants (A : Type.{1}) (A_inst : linear_ordered_field A) (u v w x y z : A)
attribute [instance] A_inst

print "======================"
print "arith_normalizer spec"
print "======================\n"
print "------------------------"
print "-- [0] Preliminaries"
print "------------------------"

print "Requires: commutative semiring structure"
print "Can exploit: add_group, linear_order, field structure, cyclic numerals, nat.sub"

print "---------------------"
print "-- [I] Basics"
print "---------------------"

print "\n-- We fuse addition\n"
#fast_arith_normalize x + x
#fast_arith_normalize x + y + 2 * x

print "\n-- We simplify 1 * x to x\n"
#fast_arith_normalize 1 * x
#fast_arith_normalize 2 * x + (-1) * x

print "\n-- We sort multiplicands\n"
#fast_arith_normalize x * y + y * x

print "\n-- Neg is multiplication by -1\n"
#fast_arith_normalize -x

print "\n-- Sub is adding the neg\n"
#fast_arith_normalize x - y

print "\n-- Zero coefficients of monomials sets monomial to zero\n"
#fast_arith_normalize x * 0 * y

print "\n-- We cancel monomials (linear-ordered only for inequalities)\n"
#fast_arith_normalize 2 * x + y = x + y
#fast_arith_normalize 2 * x + y ≤ x + y

print "\n-------------------------"
print "-- [II] Basic options"
print "-------------------------"

print "\n-- By default, we do not orient polynomials\n"
#fast_arith_normalize 2 * y - 7 = z + 2

print "\n-- With a flag set, we can orient polynomials\n"
set_option arith_normalizer.orient_polys true
#fast_arith_normalize 2 * y - 7 = z + 2
set_option arith_normalizer.orient_polys false

print "\n-- By default, we do not distribute * over +\n"
#fast_arith_normalize x * (y + z)

print "\n-- With a flag set, we can distribute * over +\n"
set_option arith_normalizer.distribute_mul true
#fast_arith_normalize x * (y + z)
set_option arith_normalizer.distribute_mul false

print "\n-------------------------"
print "-- [III] Division"
print "-------------------------"

print "\n-- We only apply a few simplifications to division"
print "-- If both are numerals, we replace with the numeral\n"
#fast_arith_normalize (5:A) / 7

print "\n-- If the second is a numeral, we replace with multiplication\n"
#fast_arith_normalize x / 2

print "\n-- If either has the form (c * x) for a numeral, we factor out the numerals (fields only)\n"
#fast_arith_normalize (2 * x) / y
#fast_arith_normalize x / (2 * y)
#fast_arith_normalize (3 * x) / (2 * y)

print "\n-- For nat, int, and any other discrete_field, x/0 ==> 0\n"
#fast_arith_normalize (5:rat)/0
#fast_arith_normalize (5:real)/0

print "\nFor other structures, if we divide by 0 we leave as is\n"
#fast_arith_normalize x / 0

print "\n-------------------------"
print "-- [IV] Coercions"
print "-------------------------"

print "\n-- We lift coerced numerals\n"
#fast_arith_normalize 1 + real.of_rat 1
#fast_arith_normalize 1 + real.of_rat (rat.of_int (int.of_nat 1))

print "\n-- We push coercions over + and *\n"
#fast_arith_normalize 1 + real.of_rat (1 + 1)
#fast_arith_normalize 1 + real.of_rat (1 * rat.of_int (2 + 3))

print "\n-------------------------"
print "-- [V] Relations"
print "-------------------------"

print "\n-- We replace all [>,≥] with [<,≤] and all strict inequalities with non-strict ones\n"
#fast_arith_normalize x > y
#fast_arith_normalize x ≥ y
#fast_arith_normalize x < y
#fast_arith_normalize x ≤ y

print "\n-- When both sides of a relation are numerals, we reduce to true or false"
#fast_arith_normalize (5:A) < 6
#fast_arith_normalize (5:A) > 6

print "\n-------------------------"
print "-- [VI] Cyclic numerals"
print "-------------------------"

print "\n-- There is an instance of [cyclic_numerals bv2] with bound=4"
print "-- We reduce numerals modulo the bound (all numerals in this section have type bv2)\n"
#fast_arith_normalize (5:bv2)

print "\n-- We reduce the numerator and denonimator separately\n"
#fast_arith_normalize (5:bv2)/6

print "\n------------------------------"
print "-- [VII] Commutative Semirings"
print "--------------------------------"

print "\n-- We do not currently do anything with sub if the type is not an add_group"
print "-- (all constants in this section are nats)\n"
constants n : nat
#fast_arith_normalize n - n
