/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "kernel/expr.h"
#include "library/type_context.h"
#include "library/tactic/simp_result.h"

namespace lean {

/** \brief Collect all nary arguments of \c e, with binary operator \c op.
    Example: <tt>(op (op a b) (op c d)) ==> [a, b, c, d]</tt>.
    In <tt>unsafe_get_app_nary_args</tt>, we assume that the pre-binary arguments are definitionally
    equal in nested applications. It will lead to a kernel type-checking error later on if this is
    not the case, and even this error may only be detected at a low-enough trust level.
    Rationale for providing the unsafe option: arithmetic. */
void get_app_nary_args(type_context & tctx, expr const & op, expr const & e, buffer<expr> & nary_args);
void unsafe_get_app_nary_args(expr const & op, expr const & e, buffer<expr> & nary_args);

optional<pair<expr, expr> > is_assoc(type_context & tctx, expr const & e);

expr mk_flat_proof(expr const & assoc, expr const & thm);

expr mk_congr_flat_proof(expr const & assoc, expr const & thm,
                         expr const & new_op, optional<expr> const & pf_op,
                         buffer<expr> const & new_nary_args,
                         buffer<optional<expr> > const & pf_nary_args);

expr mk_rewrite_assoc_proof(expr const & assoc, expr const & thm, unsigned arg_idx, expr const & pf_of_step);

void initialize_simp_util();
void finalize_simp_util();

}
