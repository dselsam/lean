/*
Copyright (c) 2016 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "library/type_context.h"
#include "library/tactic/simp_result.h"

namespace lean {
/*
======================
arith_normalizer spec
======================

------------------------
-- [0] Preliminaries
------------------------
Requires: commutative semiring structure
Can exploit: add_group, linear_order, field structure, cyclic numerals
---------------------
-- [I] Basics
---------------------

-- We fuse addition

>> x + x ==> 2 * x
>> x + y + 2 * x ==> 3 * x + y

-- We simplify 1 * x to x

>> 1 * x ==> x
>> 2 * x + -1 * x ==> x

-- We sort multiplicands

>> x * y + y * x ==> 2 * (y * x)

-- Neg is multiplication by -1

>> -x ==> -1 * x

-- Sub is adding the neg

>> x - y ==> x + -1 * y

-- Zero coefficients of monomials sets monomial to zero

>> x * 0 * y ==> 0

-- We cancel monomials (linear-ordered only for inequalities)

>> 2 * x + y = x + y ==> x = 0

-------------------------
-- [II] Basic options
-------------------------

-- By default, we do not orient polynomials

>> 2 * y - 7 = z + 2 ==> 2 * y = 9 + z

-- With a flag set, we can orient polynomials

>> 2 * y - 7 = z + 2 ==> 2 * y + -1 * z = 9

-- By default, we do not distribute * over +

>> x * (y + z) ==> x * (y + z)

-- With a flag set, we can distribute * over +

>> x * (y + z) ==> y * x + z * x

-------------------------
-- [III] Division
-------------------------

-- We only apply a few simplifications to division
-- If both are numerals, we replace with the numeral

>> 5 / 7 ==> 5/7

-- If the second is a numeral, we replace with multiplication

>> x / 2 ==> 1/2 * x

-- If either has the form (c * x) for a numeral, we factor out the numerals (fields only)

>> 2 * x / y ==> 2 * (x / y)
>> x / (2 * y) ==> 1/2 * (x / y)
>> 3 * x / (2 * y) ==> 3/2 * (x / y)

-- If we divide by 0, we replace with a special definition

>> x / 0 ==> div0 x

-------------------------
-- [IV] Coercions
-------------------------

-- We lift coerced numerals

>> 1 + real.of_rat 1 ==> 2
>> 1 + real.of_rat (rat.of_int (int.of_nat 1)) ==> 2

-- We push coercions over + and *

>> 1 + real.of_rat (1 + 1) ==> 3
>> 1 + real.of_rat (1 * rat.of_int (2 + 3)) ==> 6

-------------------------
-- [V] Relations
-------------------------

-- We replace all [>,≥] with [<,≤] and all strict inequalities with non-strict ones

>> x > y ==> ¬x ≤ y
>> x ≥ y ==> y ≤ x
>> x < y ==> ¬y ≤ x
>> x ≤ y ==> x ≤ y

-- When both sides of a relation are numerals, we reduce to true or false
-- (Q: should I skip this step to avoid axioms?)

>> 5 < 6 ==> true
>> 5 > 6 ==> false

-------------------------
-- [VI] Cyclic numerals
-------------------------

-- There is an instance of [cyclic_numerals bv2] with bound=4
-- We reduce numerals modulo the bound (all numerals in this section have type bv2)

>> 5 ==> 1

-- We reduce the numerator and denonimator separately

>> 5 / 6 ==> 1/2

------------------------------
-- [VII] Commutative Semirings
--------------------------------

-- We do not currently do anything with sub if the type is not an add_group
-- (all constants in this section are nats)

>> n - n ==> n - n
*/

expr fast_arith_normalize(type_context & tctx, expr const & e);
simp_result arith_normalize(type_context & tctx, expr const & e);

void initialize_arith_normalizer();
void finalize_arith_normalizer();

}
