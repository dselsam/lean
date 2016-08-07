/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include <string>
#include "util/sstream.h"
#include "kernel/expr.h"
#include "library/kernel_serializer.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/app_builder.h"
#include "library/tactic/ac_tactics.h"
#include "library/tactic/simplifier/util.h"

namespace lean {

static void get_app_nary_args_core(type_context * tctx_ptr, expr const & op, expr const & e, buffer<expr> & nary_args, bool unsafe) {
    lean_assert(unsafe || tctx_ptr);
    auto next_op = get_binary_op(e);
    if (next_op && (unsafe ? (get_app_fn(*next_op) == get_app_fn(op)) : tctx_ptr->is_def_eq(*next_op, op))) {
        get_app_nary_args_core(tctx_ptr, op, app_arg(app_fn(e)), nary_args, unsafe);
        get_app_nary_args_core(tctx_ptr, op, app_arg(e), nary_args, unsafe);
    } else {
        nary_args.push_back(e);
    }
}

void unsafe_get_app_nary_args(expr const & op, expr const & e, buffer<expr> & nary_args) {
    bool unsafe = true;
    get_app_nary_args_core(nullptr, op, app_arg(app_fn(e)), nary_args, unsafe);
    get_app_nary_args_core(nullptr, op, app_arg(e), nary_args, unsafe);
}

void get_app_nary_args(type_context & tctx, expr const & op, expr const & e, buffer<expr> & nary_args) {
    bool unsafe = false;
    get_app_nary_args_core(&tctx, op, app_arg(app_fn(e)), nary_args, unsafe);
    get_app_nary_args_core(&tctx, op, app_arg(e), nary_args, unsafe);
}

optional<pair<expr, expr> > is_assoc(type_context & tctx, expr const & e) {
    auto op = get_binary_op(e);
    if (!op)
        return optional<pair<expr, expr> >();
    try {
        expr assoc_class = mk_app(tctx, get_is_associative_name(), *op);
        if (auto assoc_inst = tctx.mk_class_instance(assoc_class))
            return optional<pair<expr, expr> >(mk_pair(mk_app(tctx, get_is_associative_op_assoc_name(), 3, *op, *assoc_inst), *op));
        else
            return optional<pair<expr, expr> >();
    } catch (app_builder_exception ex) {
        return optional<pair<expr, expr> >();
    }
}

expr mk_congr_bin_op(abstract_type_context & tctx, expr const & H, expr const & arg1, expr const & arg2) {
    expr eq = tctx.relaxed_whnf(tctx.infer(H));
    expr A_op, op1, op2;
    lean_verify(is_eq(eq, A_op, op1, op2));
    lean_assert(is_pi(A_op));
    expr A = binding_domain(A_op);
    level lvl  = get_level(tctx, A);
    return ::lean::mk_app({mk_constant(get_simplifier_congr_bin_op_name(), {lvl}), A, op1, op2, H, arg1, arg2});
}

expr mk_congr_bin_arg1(abstract_type_context & tctx, expr const & op, expr const & H1, expr const & arg2) {
    expr eq = tctx.relaxed_whnf(tctx.infer(H1));
    expr A, arg11, arg12;
    lean_verify(is_eq(eq, A, arg11, arg12));
    level lvl  = get_level(tctx, A);
    return ::lean::mk_app({mk_constant(get_simplifier_congr_bin_arg1_name(), {lvl}), A, op, arg11, arg12, arg2, H1});
}

expr mk_congr_bin_arg2(abstract_type_context & tctx, expr const & op, expr const & arg1, expr const & H2) {
    expr eq = tctx.relaxed_whnf(tctx.infer(H2));
    expr A, arg21, arg22;
    lean_verify(is_eq(eq, A, arg21, arg22));
    level lvl  = get_level(tctx, A);
    return ::lean::mk_app({mk_constant(get_simplifier_congr_bin_arg2_name(), {lvl}), A, op, arg1, arg21, arg22, H2});
}

expr mk_congr_bin_args(abstract_type_context & tctx, expr const & op, expr const & H1, expr const & H2) {
    expr eq1 = tctx.relaxed_whnf(tctx.infer(H1));
    expr eq2 = tctx.relaxed_whnf(tctx.infer(H2));
    expr A, A0, arg11, arg12, arg21, arg22;
    lean_verify(is_eq(eq1, A, arg11, arg12));
    lean_verify(is_eq(eq2, A0, arg21, arg22));
    lean_assert(tctx.is_def_eq(A, A0));
    level lvl  = get_level(tctx, A);
    return ::lean::mk_app({mk_constant(get_simplifier_congr_bin_args_name(), {lvl}), A, op, arg11, arg12, arg21, arg22, H1, H2});
}

expr mk_assoc_subst(abstract_type_context & tctx, expr const & old_op, expr const & new_op, expr const & pf_op, expr const & assoc) {
    expr A_op = tctx.relaxed_whnf(tctx.infer(new_op));
    lean_assert(is_pi(A_op));
    expr A = binding_domain(A_op);
    level lvl  = get_level(tctx, A);
    return ::lean::mk_app({mk_constant(get_simplifier_assoc_subst_name(), {lvl}), A, old_op, new_op, pf_op, assoc});
}

// flat-simp macro
static name * g_flat_macro_name    = nullptr;
static std::string * g_flat_opcode = nullptr;

class flat_macro_definition_cell : public macro_definition_cell {
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 2)
            throw exception(sstream() << "invalid 'flat' macro, incorrect number of arguments");
    }

public:
    flat_macro_definition_cell() {}

    virtual name get_name() const { return *g_flat_macro_name; }
    virtual expr check_type(expr const & m, abstract_type_context &, bool) const {
        check_macro(m);
        return macro_arg(m, 1);
    }

    virtual optional<expr> expand(expr const & m, abstract_type_context & tctx) const {
        check_macro(m);
        expr const & assoc      = macro_arg(m, 0);
        expr const & thm        = macro_arg(m, 1);

        expr old_e = app_arg(app_fn(thm));
        expr new_e = app_arg(thm);

        optional<expr> op = get_binary_op(old_e);
        lean_assert(op);

        pair<expr, optional<expr>> r_assoc = flat_assoc(tctx, *op, assoc, old_e);
        optional<expr> const & pf_of_assoc = r_assoc.second;

        if (!pf_of_assoc)
            return some_expr(mk_eq_refl(tctx, old_e));
        else
            return pf_of_assoc;
    }

    virtual void write(serializer & s) const {
        s.write_string(*g_flat_opcode);
    }

    virtual bool operator==(macro_definition_cell const & other) const {
        if (auto other_ptr = dynamic_cast<flat_macro_definition_cell const *>(&other)) {
            return true;
        } else {
            return false;
        }
    }

    virtual unsigned hash() const {
        return get_name().hash();
    }
};

// congr_flat macro
static name * g_congr_flat_macro_name    = nullptr;
static std::string * g_congr_flat_opcode = nullptr;

class congr_flat_macro_definition_cell : public macro_definition_cell {
    void check_macro(expr const & m) const {
        // TODO confirm 5
        if (!is_macro(m) || macro_num_args(m) < 8)
            throw exception(sstream() << "invalid 'congr_flat' macro, not enough number of arguments");
    }

public:
    congr_flat_macro_definition_cell() {}

    virtual name get_name() const { return *g_congr_flat_macro_name; }
    virtual expr check_type(expr const & m, abstract_type_context &, bool) const {
        check_macro(m);
        return macro_arg(m, 1);
    }

    simp_result congruence(abstract_type_context & tctx, expr const & e, expr const & old_op, expr const & new_op,
                           expr const & pf_op, expr const * new_args, expr const * pf_args, unsigned & i) const {
        expr arg1, arg2;
        optional<expr> op = get_binary_op(e, arg1, arg2);
        if (op && tctx.is_def_eq(*op, old_op)) {
            simp_result r(e);
            if (pf_op != expr())
                r = join_eq(tctx, r, mk_congr_bin_op(tctx, pf_op, arg1, arg2));
            simp_result r1 = congruence(tctx, arg1, old_op, new_op, pf_op, new_args, pf_args, i);
            simp_result r2 = congruence(tctx, arg2, old_op, new_op, pf_op, new_args, pf_args, i);

            expr new_e = mk_app(new_op, r1.get_new(), r2.get_new());
            if (r1.has_proof() && r2.has_proof()) {
                return join_eq(tctx, r, simp_result(new_e, mk_congr_bin_args(tctx, new_op, r1.get_proof(), r2.get_proof())));
            } else if (r1.has_proof()) {
                return join_eq(tctx, r, simp_result(new_e, mk_congr_bin_arg1(tctx, new_op, r1.get_proof(), r2.get_new())));
            } else if (r2.has_proof()) {
                return join_eq(tctx, r, simp_result(new_e, mk_congr_bin_arg2(tctx, new_op, r1.get_new(), r2.get_proof())));
            } else {
                r.update(new_e);
                return r;
            }
        } else {
            simp_result r(e);
            if (pf_args[i] == expr())
                r.update(new_args[i]);
            else
                r = join_eq(tctx, r, simp_result(new_args[i], pf_args[i]));
            i++;
            return r;
        }
    }

    simp_result flatten(abstract_type_context & tctx, expr const & new_op, expr const & new_assoc, expr const & e) const {
        return simp_result(flat_assoc(tctx, new_op, new_assoc, e));
    }

    virtual optional<expr> expand(expr const & m, abstract_type_context & tctx) const {
        check_macro(m);
        // expr mk_congr_flat_proof(expr const & assoc, expr const & thm,
        //                       expr const & new_op, optional<expr> const & pf_op,
        //                       buffer<expr> const & new_nary_args,
        //                       buffer<optional<expr> > const & pf_nary_args)

        expr const * margs      = macro_args(m);
        expr const & assoc      = margs[0];
        expr const & thm        = margs[1];
        expr const & new_op     = margs[2];
        expr const & pf_of_op   = margs[3];

        expr type = binding_domain(tctx.infer(new_op));
        level lvl = get_level(tctx, type);

        unsigned num_args = macro_num_args(m);
        unsigned arg_prefix_size = 4;

        lean_assert(num_args % 2 == 0);
        expr const * new_args = margs + arg_prefix_size;
        expr const * pf_args  = margs + arg_prefix_size + ((num_args - arg_prefix_size) / 2);

        expr old_e = app_arg(app_fn(thm));
        expr new_e = app_arg(thm);

        optional<expr> old_op = get_binary_op(old_e);
        lean_assert(old_op);

        expr new_assoc = pf_of_op == expr() ? assoc : mk_assoc_subst(tctx, *old_op, new_op, pf_of_op, assoc);

        unsigned i = 0;
        simp_result r = congruence(tctx, old_e, *old_op, new_op, pf_of_op, new_args, pf_args, i);
        r = join_eq(tctx, r, flatten(tctx, new_op, new_assoc, r.get_new()));
        return some_expr(finalize_eq(tctx, r).get_proof());
    }

    virtual void write(serializer & s) const {
        s.write_string(*g_congr_flat_opcode);
    }

    virtual bool operator==(macro_definition_cell const & other) const {
        if (auto other_ptr = dynamic_cast<congr_flat_macro_definition_cell const *>(&other)) {
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
    unsigned m_arg_idx;

    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 3)
            throw exception(sstream() << "invalid 'rewrite_assoc' macro, incorrect number of arguments");
    }

public:
    rewrite_assoc_macro_definition_cell(unsigned arg_idx): m_arg_idx(arg_idx) {}

    virtual name get_name() const { return *g_rewrite_assoc_macro_name; }
    virtual expr check_type(expr const & m, abstract_type_context &, bool) const {
        check_macro(m);
        return macro_arg(m, 1);
    }

    virtual optional<expr> expand(expr const & m, abstract_type_context &) const {
        check_macro(m);
        expr const & assoc      = macro_arg(m, 0);
        expr const & thm        = macro_arg(m, 1);
        expr const & pf_of_step = macro_arg(m, 2);

        // TODO(dhs): expand rewrite-assoc macro
        return none_expr();
    }

    virtual void write(serializer & s) const {
        s.write_string(*g_rewrite_assoc_opcode);
        s << m_arg_idx;
    }

    virtual bool operator==(macro_definition_cell const & other) const {
        if (auto other_ptr = dynamic_cast<rewrite_assoc_macro_definition_cell const *>(&other)) {
            return m_arg_idx == other_ptr->m_arg_idx;
        } else {
            return false;
        }
    }

    virtual unsigned hash() const {
        return ::lean::hash(m_arg_idx, get_name().hash());
    }
};

expr mk_flat_proof(expr const & assoc, expr const & thm) {
    expr margs[3];
    margs[0] = assoc;
    margs[1] = thm;
    macro_definition m(new flat_macro_definition_cell());
    return mk_macro(m, 2, margs);
}

expr mk_flat_macro(unsigned num_args, expr const * args) {
    lean_assert(num_args == 2);
    macro_definition m(new flat_macro_definition_cell());
    return mk_macro(m, num_args, args);
}

expr mk_congr_flat_proof(expr const & assoc, expr const & thm,
                         expr const & new_op, optional<expr> const & pf_op,
                         buffer<expr> const & new_nary_args,
                         buffer<optional<expr> > const & pf_nary_args) {
    buffer<expr> margs;
    margs.push_back(assoc);
    margs.push_back(thm);
    margs.push_back(new_op);
    margs.push_back(pf_op ? *pf_op : expr());
    for (unsigned i = 0; i < new_nary_args.size(); ++i) {
        margs.push_back(new_nary_args[i]);
    }
    for (unsigned i = 0; i < pf_nary_args.size(); ++i) {
        optional<expr> const & pf = pf_nary_args[i];
        margs.push_back(pf ? *pf : expr());
    }
    macro_definition m(new congr_flat_macro_definition_cell());
    return mk_macro(m, margs.size(), margs.data());
}

expr mk_congr_flat_macro(unsigned num_args, expr const * args) {
    lean_assert(num_args >= 8);
    macro_definition m(new congr_flat_macro_definition_cell());
    return mk_macro(m, num_args, args);
}

expr mk_rewrite_assoc_proof(expr const & assoc, expr const & thm, unsigned arg_idx, expr const & pf_of_step) {
    expr margs[3];
    margs[0] = assoc;
    margs[1] = thm;
    margs[2] = pf_of_step;
    macro_definition m(new rewrite_assoc_macro_definition_cell(arg_idx));
    return mk_macro(m, 3, margs);
}

expr mk_rewrite_assoc_macro(unsigned num_args, expr const * args, unsigned arg_idx) {
    lean_assert(num_args == 3);
    macro_definition m(new rewrite_assoc_macro_definition_cell(arg_idx));
    return mk_macro(m, 3, args);
}

// Setup and teardown
void initialize_simp_util() {
    // flat macro
    g_flat_macro_name = new name("flat");
    g_flat_opcode     = new std::string("FLAT");
    register_macro_deserializer(*g_flat_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    if (num != 3)
                                        throw corrupted_stream_exception();
                                    return mk_flat_macro(num, args);
                                });

    // congr_flat macro
    g_congr_flat_macro_name = new name("congr_flat");
    g_congr_flat_opcode     = new std::string("CONGR_FLAT");
    register_macro_deserializer(*g_congr_flat_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    if (num < 8)
                                        throw corrupted_stream_exception();
                                    return mk_congr_flat_macro(num, args);
                                });

    // rewrite_assoc macro
    g_rewrite_assoc_macro_name = new name("rewrite_assoc");
    g_rewrite_assoc_opcode     = new std::string("REWRITE_ASSOC");
    register_macro_deserializer(*g_rewrite_assoc_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    if (num != 3)
                                        throw corrupted_stream_exception();
                                    unsigned arg_idx;
                                    d >> arg_idx;
                                    return mk_rewrite_assoc_macro(num, args, arg_idx);
                                });
}

void finalize_simp_util() {
    // rewrite_assoc macro
    delete g_rewrite_assoc_macro_name;
    delete g_rewrite_assoc_opcode;

    // congr_flat macro
    delete g_congr_flat_macro_name;
    delete g_congr_flat_opcode;

    // flat macro
    delete g_flat_macro_name;
    delete g_flat_opcode;
}
}
