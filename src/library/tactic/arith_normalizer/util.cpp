/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "library/util.h"
#include "library/constants.h"
#include "util/name_hash_map.h"
#include "library/mpq_macro.h"
#include "library/tactic/arith_normalizer/util.h"

namespace lean {

static name_hash_map<head_type> * g_head_type_map = nullptr;

head_type get_head_type(expr const & e) {
    if (!is_constant(e))
        return head_type::OTHER;

    auto it = g_head_type_map->find(const_name(e));
    if (it == g_head_type_map->end()) {
        return head_type::OTHER;
    } else {
        return it->second;
    }
}

expr mk_nary_app(expr const & fn, buffer<expr> const & args) {
    lean_assert(!args.empty());
    expr e = args.back();
    for (int i = args.size() - 2; i >= 0; --i) {
        e = mk_app(fn, args[i], e);
    }
    return e;
}

expr get_power_product(expr const & monomial) {
    expr lhs, rhs;
    if (is_mul(monomial, lhs, rhs) && is_mpq_macro(lhs)) {
        return rhs;
    } else {
        return monomial;
    }
}

expr get_power_product(expr const & monomial, mpq & num) {
    expr lhs, rhs;
    if (is_mul(monomial, lhs, rhs) && is_mpq_macro(lhs, num)) {
        return rhs;
    } else {
        num = 1;
        return monomial;
    }
}

expr mk_mod_mpq_macro(arith_instance_manager & im, mpq const & coeff) {
    if (auto const & bound = im.has_cyclic_numerals()) {
        mpz coeff_n = coeff.get_numerator();
        coeff_n %= *bound;
        mpq c(coeff_n);
        mpz coeff_d = coeff.get_denominator();
        if (coeff_d != 1) {
            coeff_d %= *bound;
            c /= coeff_d;
        }
        return mk_mpq_macro(c, im.get_type());
    } else {
        return mk_mpq_macro(coeff, im.get_type());
    }
}

expr mk_monomial(arith_instance_manager & im, mpq const & coeff) {
    return mk_mod_mpq_macro(im, coeff);
}

expr mk_monomial(arith_instance_manager & im, mpq const & coeff, expr const & power_product) {
    if (coeff == 1) {
        return power_product;
    } else {
        expr c = mk_mod_mpq_macro(im, coeff);
        return mk_app(im.get_mul(), c, power_product);
    }
}

expr mk_polynomial(arith_instance_manager & im, mpq const & coeff, buffer<expr> const & monomials) {
    expr c = mk_mod_mpq_macro(im, coeff);
    if (monomials.empty()) {
        return c;
    } else if (coeff.is_zero()) {
        return mk_polynomial(im, monomials);
    } else {
        return mk_app(im.get_add(), c, mk_nary_app(im.get_add(), monomials));
    }
}

expr mk_polynomial(arith_instance_manager & im, buffer<expr> const & monomials) {
    if (monomials.empty())
        return mk_mod_mpq_macro(im, mpq(0));

    return mk_nary_app(im.get_add(), monomials);
}

// Setup and teardown

void initialize_arith_normalizer_util() {
    // Head types
    g_head_type_map = new name_hash_map<head_type>({
            {get_eq_name(), head_type::EQ},
            {get_le_name(), head_type::LE},
            {get_ge_name(), head_type::GE},
            {get_lt_name(), head_type::LT},
            {get_gt_name(), head_type::GT},
            {get_add_name(), head_type::ADD},
            {get_mul_name(), head_type::MUL},
            {get_sub_name(), head_type::SUB},
            {get_div_name(), head_type::DIV},
            {get_neg_name(), head_type::NEG},
            {get_zero_name(), head_type::ZERO},
            {get_one_name(), head_type::ONE},
            {get_bit0_name(), head_type::BIT0},
            {get_bit1_name(), head_type::BIT1},
            {get_int_of_nat_name(), head_type::INT_OF_NAT},
            {get_rat_of_int_name(), head_type::RAT_OF_INT},
            {get_real_of_rat_name(), head_type::REAL_OF_RAT}
        });
}

void finalize_arith_normalizer_util() {
    // Head types
    delete g_head_type_map;
}

}
