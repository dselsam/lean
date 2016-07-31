/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "util/sstream.h"
#include "kernel/expr.h"
#include "library/kernel_serializer.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/app_builder.h"
#include "library/tactic/simplifier/util.h"

namespace lean {

optional<expr> is_assoc(type_context & tctx, expr const & e) {
    auto op = get_binary_op(e);
    if (!op)
        return none_expr();
    try {
        expr assoc_class = mk_app(tctx, get_is_associative_name(), *op);
        if (auto assoc_inst = tctx.mk_class_instance(assoc_class))
            return some_expr(mk_app(tctx, get_is_associative_op_assoc_name(), 3, *assoc_inst));
        else
            return none_expr();
    } catch (app_builder_exception ex) {
        return none_expr();
    }
}

optional<expr> is_comm(type_context & tctx, expr const & e) {
    auto op = get_binary_op(e);
    if (!op)
        return none_expr();
    try {
        expr comm_class = mk_app(tctx, get_is_commutative_name(), *op);
        if (auto comm_inst = tctx.mk_class_instance(comm_class))
            return some_expr(mk_app(tctx, get_is_commutative_op_comm_name(), 3, *comm_inst));
        else
            return none_expr();
    } catch (app_builder_exception ex) {
        return none_expr();
    }
}

// Rewrite-assoc macro
static name * g_rewrite_assoc_macro_name    = nullptr;
static std::string * g_rewrite_assoc_opcode = nullptr;

class rewrite_assoc_macro_definition_cell : public macro_definition_cell {
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 3)
            throw exception(sstream() << "invalid 'rewrite_assoc' macro, incorrect number of arguments");
    }

public:
    rewrite_assoc_macro_definition_cell() {}

    virtual name get_name() const { return *g_rewrite_assoc_macro_name; }
    virtual expr check_type(expr const & m, abstract_type_context &, bool) const {
        check_macro(m);
        return macro_arg(m, 1);
    }

    virtual optional<expr> expand(expr const & m, abstract_type_context &) const {
        check_macro(m);
        // TODO(dhs): expand rewrite-assoc macro
        return none_expr();
    }

    virtual void write(serializer & s) const {
        s.write_string(*g_rewrite_assoc_opcode);
    }

    virtual bool operator==(macro_definition_cell const & other) const {
        if (auto other_ptr = dynamic_cast<rewrite_assoc_macro_definition_cell const *>(&other)) {
            return true;
        } else {
            return false;
        }
    }

    virtual unsigned hash() const {
        return get_name().hash();
    }
};

expr mk_rewrite_assoc_macro(unsigned num_args, expr const * args) {
    lean_assert(num_args == 3);
    macro_definition m(new rewrite_assoc_macro_definition_cell());
    return mk_macro(m, 3, args);
}

expr mk_rewrite_assoc_macro(expr const & assoc, expr const & thm, expr const & pf_of_step) {
    expr margs[3];
    margs[0] = assoc;
    margs[1] = thm;
    margs[2] = pf_of_step;
    macro_definition m(new rewrite_assoc_macro_definition_cell());
    return mk_macro(m, 3, margs);
}

void initialize_simp_util() {
    // rewrite_assoc macro
    g_rewrite_assoc_macro_name = new name("rewrite_assoc");
    g_rewrite_assoc_opcode     = new std::string("REWRITE_ASSOC");
    register_macro_deserializer(*g_rewrite_assoc_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    if (num != 3)
                                        throw corrupted_stream_exception();
                                    return mk_rewrite_assoc_macro(num, args);
                                });
}

void finalize_simp_util() {
    // rewrite_assoc macro
    delete g_rewrite_assoc_macro_name;
    delete g_rewrite_assoc_opcode;
}

}
