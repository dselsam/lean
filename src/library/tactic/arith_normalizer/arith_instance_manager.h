/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "util/sstream.h"
#include "library/type_context.h"

namespace lean {

// TODO(dhs): what should the lifecycle of this be?
class arith_instance_manager {
    type_context & m_tctx;

    expr m_type;
    level m_level;

    // For boolean queries
    optional<bool> m_is_field, m_is_discrete_field, m_is_comm_ring, m_is_linear_ordered_comm_ring;
    optional<bool> m_is_comm_semiring, m_is_linear_ordered_semiring, m_is_add_group;

    optional<bool> m_has_cyclic_numerals;
    mpz m_numeral_bound;

    // Partial applications
    expr m_zero, m_one;
    expr m_bit0, m_bit1;
    expr m_add, m_mul, m_div, m_sub, m_neg;
    expr m_eq, m_le, m_ge;

    bool null(expr const & e) { return e == expr(); }

public:
    arith_instance_manager(type_context & tctx, expr const & type);
    arith_instance_manager(type_context & tctx, expr const & type, level const & l);

    expr get_type() const { return m_type; }

    bool is_add_group();
    bool is_comm_semiring();
    bool is_comm_ring();
    bool is_linear_ordered_semiring();
    bool is_linear_ordered_comm_ring();
    bool is_field();
    bool is_discrete_field();
    optional<mpz> has_cyclic_numerals();

    expr get_zero();
    expr get_one();
    expr get_bit0();
    expr get_bit1();
    expr get_add();
    expr get_mul();
    expr get_sub();
    expr get_div();
    expr get_neg();
    expr get_eq();
    expr get_le();
    expr get_ge();
    expr get_lt();
    expr get_gt();
};

void initialize_arith_normalizer_instance_manager();
void finalize_arith_normalizer_instance_manager();

}
