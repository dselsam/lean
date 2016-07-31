/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "library/arith_instance_manager.h"
#include "library/tactic/simplifier/simplifier.h"

namespace lean {

struct prop_simplifier_options {
    bool m_elim_and;
    prop_simplifier_options(options const & opts);
};

class prop_simplifier {
private:
    type_context                 & m_tctx;
    prop_simplifier_options        m_options;

    optional<expr> simplify_eq_core(expr const & type, expr const & lhs, expr const & rhs);
    optional<expr> simplify_not_core(expr const & e);
    optional<expr> simplify_and_core(buffer<expr> & nary_args);
    optional<expr> simplify_or_core(buffer<expr> & nary_args);

public:

    simp_result simplify_eq(expr const & e);
    simp_result simplify_iff(expr const & e);
    simp_result simplify_not(expr const & e);
    simp_result simplify_and(expr const & e);
    simp_result simplify_or(expr const & e);

    prop_simplifier(type_context & tctx): m_tctx(tctx), m_options(tctx.get_options()) {}
};

void initialize_prop_simplifier();
void finalize_prop_simplifier();
}
