/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "kernel/expr.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/app_builder.h"
#include "library/tactic/simplifier/util.h"

namespace lean {

optional<expr> is_assoc(type_context & tctx, expr const & e) {
    auto op = get_binary_op(e);
    if (!op)
        return none_expr();
    expr assoc_class = mk_app(tctx, get_is_associative_name(), e);
    if (auto assoc_inst = tctx.mk_class_instance(assoc_class))
        return some_expr(mk_app(tctx, get_is_associative_op_assoc_name(), *assoc_inst));
    else
        return none_expr();
}

optional<expr> is_comm(type_context & tctx, expr const & e) {
    auto op = get_binary_op(e);
    if (!op)
        return none_expr();
    expr comm_class = mk_app(tctx, get_is_commutative_name(), e);
    if (auto comm_inst = tctx.mk_class_instance(comm_class))
        return some_expr(mk_app(tctx, get_is_commutative_op_comm_name(), *comm_inst));
    else
        return none_expr();
}


void initialize_simp_util() {}
void finalize_simp_util() {}

}
