/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "kernel/expr.h"
#include "library/tactic/arith_normalizer/arith_instance_manager.h"

namespace lean {

expr mk_nary_app(expr const & fn, buffer<expr> const & args);
expr get_power_product(expr const & monomial);
expr get_power_product(expr const & monomial, mpq & num);

enum class head_type {
    EQ, LE, GE,
        LT, GT,
        ADD, MUL,
        SUB, DIV,
        NEG,
        ZERO, ONE, BIT0, BIT1,
        INT_OF_NAT, RAT_OF_INT, REAL_OF_RAT,
        OTHER
        };

head_type get_head_type(expr const & e);

enum rel_kind { EQ, LE, LT };

struct arith_normalize_options {
    bool m_distribute_mul, m_fuse_mul, m_normalize_div, m_orient_polys, m_profile;
    arith_normalize_options(options const & o);
};

expr mk_mod_mpq_macro(arith_instance_manager & im, mpq const & coeff);
expr mk_monomial(arith_instance_manager & im, mpq const & coeff);
expr mk_monomial(arith_instance_manager & im, mpq const & coeff, expr const & power_product);
expr mk_polynomial(arith_instance_manager & im, mpq const & coeff, buffer<expr> const & monomials);
expr mk_polynomial(arith_instance_manager & im, buffer<expr> const & monomials);

void initialize_arith_normalizer_util();
void finalize_arith_normalizer_util();

}
