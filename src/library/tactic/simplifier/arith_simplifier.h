/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "library/arith_instance_manager.h"
#include "library/tactic/simplifier/simplifier.h"

namespace lean {

struct arith_simplifier_options {
    bool m_distribute_mul;
    arith_simplifier_options(options const & opts);
};

class arith_simplifier {
private:
    // Note: we use a [type_context *] instead of a [type_context &]
    // because some consumers may not have a [type_context] and may only want to
    // simplify concrete arith types.
    type_context                 * m_tctx_ptr;
    arith_simplifier_options       m_options;
    arith_instance_info_ref        m_arith_info;

public:
    optional<simp_result>   simplify_eq(expr const & prefix, buffer<expr> const & args);

    optional<simp_result>   simplify_lt(expr const & prefix, buffer<expr> const & args);
    optional<simp_result>   simplify_gt(expr const & prefix, buffer<expr> const & args);
    optional<simp_result>   simplify_le(expr const & prefix, buffer<expr> const & args);
    optional<simp_result>   simplify_ge(expr const & prefix, buffer<expr> const & args);

    optional<simp_result>   simplify_add(expr const & prefix, buffer<expr> const & args);
    optional<simp_result>   simplify_mul(expr const & prefix, buffer<expr> const & args);

    optional<simp_result>   simplify_neg(expr const & prefix, buffer<expr> const & args);
    optional<simp_result>   simplify_sub(expr const & prefix, buffer<expr> const & args);
    optional<simp_result>   simplify_inv(expr const & prefix, buffer<expr> const & args);
    optional<simp_result>   simplify_div(expr const & prefix, buffer<expr> const & args);

    optional<simp_result>   simplify_numeral(expr const & prefix, buffer<expr> const & args);

    optional<simp_result>   simplify_int_of_nat(expr const & prefix, buffer<expr> const & args);
    optional<simp_result>   simplify_rat_of_int(expr const & prefix, buffer<expr> const & args);
    optional<simp_result>   simplify_real_of_rat(expr const & prefix, buffer<expr> const & args);

    // New interface
//    simp_result simplify_

    arith_simplifier(type_context & tctx): m_tctx_ptr(&tctx), m_options(tctx.get_options()) {}
};

void initialize_arith_simplifier();
void finalize_arith_simplifier();
}
