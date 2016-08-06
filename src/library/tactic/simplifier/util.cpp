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

optional<pair<expr, expr> > is_assoc(type_context & tctx, name const & rel, expr const & e) {
    auto op = get_binary_op(e);
    if (!op)
        return optional<pair<expr, expr> >();
    // TODO(dhs): optimized helper for instantiating a relation given a single element of a given type
    expr e_rel = app_fn(app_fn(mk_rel(tctx, rel, e, e)));
    try {
        expr assoc_class = mk_app(tctx, get_is_associative_name(), e_rel, *op);
        if (auto assoc_inst = tctx.mk_class_instance(assoc_class))
            return optional<pair<expr, expr> >(mk_pair(mk_app(tctx, get_is_associative_op_assoc_name(), 4, e_rel, *op, *assoc_inst), *op));
        else
            return optional<pair<expr, expr> >();
    } catch (app_builder_exception ex) {
        return optional<pair<expr, expr> >();
    }
}

// flat-simp macro
static name * g_flat_simp_macro_name    = nullptr;
static std::string * g_flat_simp_opcode = nullptr;

class flat_simp_macro_definition_cell : public macro_definition_cell {
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 3)
            throw exception(sstream() << "invalid 'flat_simp' macro, incorrect number of arguments");
    }

public:
    flat_simp_macro_definition_cell() {}

    virtual name get_name() const { return *g_flat_simp_macro_name; }
    virtual expr check_type(expr const & m, abstract_type_context &, bool) const {
        check_macro(m);
        return macro_arg(m, 1);
    }

    virtual optional<expr> expand(expr const & m, abstract_type_context &) const {
        check_macro(m);
        // TODO(dhs): expand flat-simp macro
        return none_expr();
    }

    virtual void write(serializer & s) const {
        s.write_string(*g_flat_simp_opcode);
    }

    virtual bool operator==(macro_definition_cell const & other) const {
        if (auto other_ptr = dynamic_cast<flat_simp_macro_definition_cell const *>(&other)) {
            return true;
        } else {
            return false;
        }
    }

    virtual unsigned hash() const {
        return get_name().hash();
    }
};

// congr_flat_simp macro
static name * g_congr_flat_simp_macro_name    = nullptr;
static std::string * g_congr_flat_simp_opcode = nullptr;

class congr_flat_simp_macro_definition_cell : public macro_definition_cell {
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) < 5)
            throw exception(sstream() << "invalid 'congr_flat_simp' macro, not enough number of arguments");
    }

public:
    congr_flat_simp_macro_definition_cell() {}

    virtual name get_name() const { return *g_congr_flat_simp_macro_name; }
    virtual expr check_type(expr const & m, abstract_type_context &, bool) const {
        check_macro(m);
        return macro_arg(m, 1);
    }

    virtual optional<expr> expand(expr const & m, abstract_type_context &) const {
        check_macro(m);
        // TODO(dhs): expand flat-simp macro
        return none_expr();
    }

    virtual void write(serializer & s) const {
        s.write_string(*g_congr_flat_simp_opcode);
    }

    virtual bool operator==(macro_definition_cell const & other) const {
        if (auto other_ptr = dynamic_cast<congr_flat_simp_macro_definition_cell const *>(&other)) {
            return true;
        } else {
            return false;
        }
    }

    virtual unsigned hash() const {
        return get_name().hash();
    }
};

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

expr mk_flat_simp_macro(expr const & assoc, expr const & thm, optional<expr> pf_of_simp) {
    expr margs[3];
    margs[0] = assoc;
    margs[1] = thm;
    margs[2] = pf_of_simp ? *pf_of_simp : expr();
    macro_definition m(new flat_simp_macro_definition_cell());
    return mk_macro(m, 3, margs);
}

expr mk_flat_simp_macro(unsigned num_args, expr const * args) {
    lean_assert(num_args == 3);
    macro_definition m(new flat_simp_macro_definition_cell());
    return mk_macro(m, num_args, args);
}

expr mk_congr_flat_simp_macro(expr const & assoc, expr const & thm, optional<expr> const & pf_of_simp,
                              optional<expr> const & pf_op, buffer<optional<expr> > const & pf_nary_args) {
    unsigned num_macro_args = 4 + pf_nary_args.size();
    expr margs[num_macro_args];
    margs[0] = assoc;
    margs[1] = thm;
    margs[2] = pf_of_simp ? *pf_of_simp : expr();
    margs[3] = pf_op ? *pf_op : expr();
    for (unsigned i = 0; i < pf_nary_args.size(); ++i) {
        optional<expr> const & pf = pf_nary_args[i];
        margs[i+4] = pf ? *pf : expr();
    }
    macro_definition m(new congr_flat_simp_macro_definition_cell());
    return mk_macro(m, num_macro_args, margs);
}

expr mk_congr_flat_simp_macro(unsigned num_args, expr const * args) {
    lean_assert(num_args >= 6);
    macro_definition m(new congr_flat_simp_macro_definition_cell());
    return mk_macro(m, num_args, args);
}

expr mk_rewrite_assoc_macro(expr const & assoc, expr const & thm, expr const & pf_of_step) {
    expr margs[3];
    margs[0] = assoc;
    margs[1] = thm;
    margs[2] = pf_of_step;
    macro_definition m(new rewrite_assoc_macro_definition_cell());
    return mk_macro(m, 3, margs);
}

expr mk_rewrite_assoc_macro(unsigned num_args, expr const * args) {
    lean_assert(num_args == 3);
    macro_definition m(new rewrite_assoc_macro_definition_cell());
    return mk_macro(m, 3, args);
}

// Setup and teardown
void initialize_simp_util() {
    // flat_simp macro
    g_flat_simp_macro_name = new name("flat_simp");
    g_flat_simp_opcode     = new std::string("FLAT_SIMP");
    register_macro_deserializer(*g_flat_simp_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    if (num != 3)
                                        throw corrupted_stream_exception();
                                    return mk_flat_simp_macro(num, args);
                                });

    // congr_flat_simp macro
    g_congr_flat_simp_macro_name = new name("congr_flat_simp");
    g_congr_flat_simp_opcode     = new std::string("CONGR_FLAT_SIMP");
    register_macro_deserializer(*g_congr_flat_simp_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    if (num < 6)
                                        throw corrupted_stream_exception();
                                    return mk_congr_flat_simp_macro(num, args);
                                });

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

    // congr_flat_simp macro
    delete g_congr_flat_simp_macro_name;
    delete g_congr_flat_simp_opcode;

    // flat_simp macro
    delete g_flat_simp_macro_name;
    delete g_flat_simp_opcode;

}
}
