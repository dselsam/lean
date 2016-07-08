/*
Copyright (c) 2016 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include <functional>
#include "util/optional.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/abstract.h"
#include "kernel/expr_maps.h"
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/expr_lt.h"
#include "library/num.h"
#include "library/util.h"
#include "library/norm_num.h"
#include "library/defeq_canonizer.h"
#include "library/app_builder.h"
#include "library/fun_info.h"
#include "library/sorry.h"
#include "library/kernel_serializer.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/arith_normalizer.h"

#ifndef LEAN_DEFAULT_ARITH_NORMALIZER_DISTRIBUTE_MUL
#define LEAN_DEFAULT_ARITH_NORMALIZER_DISTRIBUTE_MUL false
#endif
#ifndef LEAN_DEFAULT_ARITH_NORMALIZER_FUSE_MUL
#define LEAN_DEFAULT_ARITH_NORMALIZER_FUSE_MUL false
#endif
#ifndef LEAN_DEFAULT_ARITH_NORMALIZER_NORMALIZE_DIV
#define LEAN_DEFAULT_ARITH_NORMALIZER_NORMALIZE_DIV false
#endif
#ifndef LEAN_DEFAULT_ARITH_NORMALIZER_ORIENT_POLYS
#define LEAN_DEFAULT_ARITH_NORMALIZER_ORIENT_POLYS false
#endif

namespace lean {

// Options
static name * g_arith_normalizer_distribute_mul = nullptr;
static name * g_arith_normalizer_fuse_mul       = nullptr;
static name * g_arith_normalizer_normalize_div  = nullptr;
static name * g_arith_normalizer_orient_polys   = nullptr;

static bool get_arith_normalizer_distribute_mul(options const & o) {
    return o.get_bool(*g_arith_normalizer_distribute_mul, LEAN_DEFAULT_ARITH_NORMALIZER_DISTRIBUTE_MUL);
}

static bool get_arith_normalizer_fuse_mul(options const & o) {
    return o.get_bool(*g_arith_normalizer_fuse_mul, LEAN_DEFAULT_ARITH_NORMALIZER_FUSE_MUL);
}

static bool get_arith_normalizer_normalize_div(options const & o) {
    return o.get_bool(*g_arith_normalizer_normalize_div, LEAN_DEFAULT_ARITH_NORMALIZER_NORMALIZE_DIV);
}

static bool get_arith_normalizer_orient_polys(options const & o) {
    return o.get_bool(*g_arith_normalizer_orient_polys, LEAN_DEFAULT_ARITH_NORMALIZER_ORIENT_POLYS);
}

struct arith_normalize_options {
    bool m_distribute_mul, m_fuse_mul, m_normalize_div, m_orient_polys;
    arith_normalize_options(options const & o):
        m_distribute_mul(get_arith_normalizer_distribute_mul(o)),
        m_fuse_mul(get_arith_normalizer_fuse_mul(o)),
        m_normalize_div(get_arith_normalizer_normalize_div(o)),
        m_orient_polys(get_arith_normalizer_orient_polys(o))
        {}

    bool distribute_mul() const { return m_distribute_mul; }
    bool fuse_mul() const { return m_fuse_mul; }
    bool normalize_div() const { return m_normalize_div; }
    bool orient_polys() const { return m_orient_polys; }
};


// Helpers

static void get_flattened_nary_summands(expr const & e, buffer<expr> & args) {
    // TODO(dhs): do I process subtraction here?
    expr arg1, arg2;
    if (is_add(e, arg1, arg2)) {
        get_flattened_nary_summands(arg1, args);
        get_flattened_nary_summands(arg2, args);
    } else {
        args.push_back(e);
    }
}

static bool is_numeral_expr(expr const & e, mpq & num) {
    lean_assert(is_numeral_expr(e));
    buffer<expr, 4> args;
    expr f = get_app_args(e, args)/
    if (!is_constant(f))
        return false;

    mpq rhs;
    if (const_name(f) == get_add_name() && args.size() == 4) {
        if (!is_numeral_expr(args[2], num) || !is_numeral_expr(args[3], rhs))
            return false;
        num += rhs;
    } else if (const_name(f) == get_mul_name() && args.size() == 4) {
        if (!is_numeral_expr(args[2], num) || !is_numeral_expr(args[3], rhs))
            return false;
        num *= rhs;
    } else if (const_name(f) == get_sub_name() && args.size() == 4) {
        if (!is_numeral_expr(args[2], num) || !is_numeral_expr(args[3], rhs))
            return false;
        num -= rhs;
    } else if (const_name(f) == get_div_name() && args.size() == 4) {
        if (!is_numeral_expr(args[2], num) || !is_numeral_expr(args[3], rhs) || rhs.is_zero())
            return false;
        num /= rhs;
    } else if (const_name(f) == get_neg_name() && args.size() == 3) {
        if (!is_numeral_expr(args[2], num))
            return false;
        num.neg();
    } else if (auto n = to_num(e)) {
        num = *n;
    } else {
        return false;
    }
    return true;
}

// Fast arith_normalizer

enum class head_type {
    EQ, LE, GE,
    // TODO(dhs): LT, GT
    ADD, MUL,
    SUB, DIV,
    INT_OF_NAT, RAT_OF_INT, REAL_OF_RAT,
    OTHER
        };

enum rel_kind { EQ, LE, GE };

enum class norm_status { DONE, FAILED };

static inline head_type get_head_type(expr const & op) {
    if (!is_constant(op)) return head_type::OTHER;

    else if (const_name(op) == get_eq_name()) return head_type::EQ;

    else if (const_name(op) == get_le_name()) return head_type::LE;
    else if (const_name(op) == get_ge_name()) return head_type::GE;

    else if (const_name(op) == get_lt_name()) return head_type::LT;
    else if (const_name(op) == get_gt_name()) return head_type::GT;

    else if (const_name(op) == get_add_name()) return head_type::ADD;
    else if (const_name(op) == get_mul_name()) return head_type::MUL;

    else if (const_name(op) == get_sub_name()) return head_type::SUB;
    else if (const_name(op) == get_div_name()) return head_type::DIV;

    else if (const_name(op) == get_int_of_nat_name()) return head_type::INT_OF_NAT;
    else if (const_name(op) == get_rat_of_int_name()) return head_type::RAT_OF_INT;
    else if (const_name(op) == get_real_of_rat_name()) return head_type::REAL_OF_RAT;

    else return head_type::OTHER;
}

class fast_arith_normalize_fn {
    type_context            m_tctx;
    arith_normalize_options m_options;

    optional<expr> fast_normalize_numeral_expr(expr const & e) {
        // TODO(dhs): PERF
        // try/catch too slow
        // also need a norm-num that does not bother producing proofs
        // also need a quick is_numeral check
        try {
            pair<expr, expr> result = mk_norm_num(m_tctx, e);
            return some_expr(result.first);
        } catch (exception & e) {
            return none_expr();
        }
    }

    norm_status normalize_app_core(expr const & op, buffer<expr> const & args, expr & result) {
        // TODO(dhs): implement
        switch (get_head_type(op)) {
        case head_type::EQ:

        case head_type::LE:
        case head_type::GE:

        case head_type::ADD:
        case head_type::MUL:

        case head_type::SUB:
        case head_type::DIV:

        case head_type::INT_OF_NAT:
        case head_type::RAT_OF_INT:
        case head_type::REAL_OF_RAT:

        case head_type::OTHER:
            break;
        }
        return norm_status::FAILED;
    }

    expr normalize_app(expr const & e) {
        lean_assert(is_app(e));
        if (auto num = fast_normalize_numeral_expr(e)) { return *num; }

        expr result = e;
        buffer<expr> args;
        expr op = get_app_args(e, args);

        normalize_app_core(op, args, result);
        return result;
    }

    norm_status fuse_and_cancel_monomials(expr const & lhs, expr const & rhs, expr & new_lhs, expr & new_rhs) {
        buffer<expr> lhs_summands;
        buffer<expr> rhs_summands;
        get_flattened_nary_summands(lhs, lhs_summands);
        get_flattened_nary_summands(lhs, rhs_summands);

        // TODO(dhs): expr_struct_set?
        expr_set visited_power_products;
        expr_set multi_visited_power_products;
        bool some_pp_multi_visited = false;

        mpq coeff;
        mpq num;
        unsigned num_coeff = 0;
        for (expr const & arg : lhs_summands) {
            expr monomial = fast_normalize(arg);
            if (is_numeral_expr(monomial, num)) {
                coeff += num;
                num_coeff++;
            } else {
                expr power_product = get_power_product(monomial);
                visited_monomials.insert(power_product);
            }
        }

        for (expr const & arg : rhs_summands) {
            expr monomial = fast_normalize(arg);
            if (is_numeral_expr(monomial, num)) {
                coeff -= num;
                num_coeffs++;
            } else {
                expr power_product = get_power_product(monomial);
                if (visited_power_products.contains(power_product)) {
                    multi_visited_power_products.insert(power_product);
                    some_pp_multi_visited = true;
                }
            }
        }





//        if (m_options.orient_polys() && num_coeffs == 0 && is_numeral_expr(rhs))
//            return norm_status::FAILED;



    }

    norm_status normalize_rel_core(expr const & lhs, expr const & rhs, expr & result) {
        expr new_lhs, new_rhs;
        norm_status st = fuse_and_cancel_monomials(lhs, rhs, new_lhs, new_rhs);

        // TODO(dhs): if both sides are numerals, then reduce to true or false
        // TODO(dhs): bounds
        // TODO(dhs): gcd stuff
        return st;
    }




    }

    expr normalize_rel(expr const & e, rel_type rt) {
        expr result = e;
        buffer<expr> args;
        expr op = get_app_args(e, args);

        normalize_rel_core(op, args, result);
        return result;
    }

    expr normalize_eq(expr const & e) {
        lean_assert(is_eq(e));
        return normalize_rel(e, rel_type::EQ);
    }

    expr normalize_le(expr const & e) {
        lean_assert(is_le(e));
        return normalize_rel(e, rel_type::LE);
    }

    expr normalize_ge(expr const & e) {
        lean_assert(is_ge(e));
        return normalize_rel(e, rel_type::GE);
    }


};


// Macro for trusting the fast normalizer
static name * g_arith_normalizer_macro_name    = nullptr;
static std::string * g_arith_normalizer_opcode = nullptr;

class arith_normalizer_macro_definition_cell : public macro_definition_cell {
    // TODO(dhs): what will I need to trigger the tactic framework from the kernel?
    /*
    environment     m_env
    local_context   m_lctx;
    metavar_context m_mctx;
    expr            m_thm;
    */

    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 1)
            throw exception(sstream() << "invalid 'arith_normalizer' macro, incorrect number of arguments");
    }

public:
    arith_normalizer_macro_definition_cell() {}

    virtual name get_name() const { return *g_arith_normalizer_macro_name; }
    virtual expr check_type(expr const & m, abstract_type_context & ctx, bool infer_only) const {
        check_macro(m);
        return macro_arg(m, 0);
    }

    virtual optional<expr> expand(expr const & m, abstract_type_context & ctx) const {
        check_macro(m);
        // TODO(dhs): create a new type context and run slow_arith_normalizer
        return none_expr();
    }

    virtual void write(serializer & s) const {
        s.write_string(*g_arith_normalizer_opcode);
    }

    virtual bool operator==(macro_definition_cell const & other) const {
        // TODO(dhs): what is this used for?
        if (auto other_ptr = dynamic_cast<arith_normalizer_macro_definition_cell const *>(&other)) {
            return true;
        } else {
            return false;
        }
    }

    virtual unsigned hash() const {
        return get_name().hash();
    }
};

static expr mk_arith_normalizer_macro(expr const & thm) {
    macro_definition m(new arith_normalizer_macro_definition_cell());
    return mk_macro(m, 1, &thm);
}

// Entry points
expr fast_arith_normalize(type_context & tctx, expr const & lhs) {
    return lhs;
}

simp_result arith_normalize(type_context & tctx, expr const & lhs) {
    expr rhs = fast_arith_normalize(tctx, lhs);
    expr pf = mk_arith_normalizer_macro(mk_eq(tctx, lhs, rhs));
    return simp_result(rhs, pf);
}

// VM

vm_obj tactic_arith_normalize(vm_obj const & e, vm_obj const & s0) {
    tactic_state const & s   = to_tactic_state(s0);
    try {
        type_context tctx = mk_type_context_for(s, transparency_mode::None);
        expr lhs = to_expr(e);
        simp_result result = arith_normalize(tctx, lhs);
        if (result.has_proof()) {
            return mk_tactic_success(mk_vm_pair(to_obj(result.get_new()), to_obj(result.get_proof())), s);
        } else {
            return mk_tactic_exception("arith_normalize tactic failed to simplify", s);
        }
    } catch (exception & e) {
        return mk_tactic_exception(e, s);
    }
}


// Setup and teardown

void initialize_arith_normalizer() {
    // Options names
    g_arith_normalizer_distribute_mul     = new name{"arith_normalizer", "distribute_mul"};
    g_arith_normalizer_fuse_mul           = new name{"arith_normalizer", "fuse_mul"};
    g_arith_normalizer_normalize_div      = new name{"arith_normalizer", "normalize_div"};
    g_arith_normalizer_orient_polys       = new name{"arith_normalizer", "orient_polys"};

    // Register options
    register_bool_option(*g_arith_normalizer_distribute_mul, LEAN_DEFAULT_ARITH_NORMALIZER_DISTRIBUTE_MUL,
                         "(arith_normalizer) distribute mul over add");
    register_bool_option(*g_arith_normalizer_fuse_mul, LEAN_DEFAULT_ARITH_NORMALIZER_FUSE_MUL,
                         "(arith_normalizer) fuse (x * x) ==> x^2");
    register_bool_option(*g_arith_normalizer_normalize_div, LEAN_DEFAULT_ARITH_NORMALIZER_NORMALIZE_DIV,
                         "(arith_normalizer) (x / z) * y ==> (x * y) / z");
    register_bool_option(*g_arith_normalizer_orient_polys, LEAN_DEFAULT_ARITH_NORMALIZER_ORIENT_POLYS,
                         "(arith_normalizer) x + y + z = w + 2 ==> x + y + z - w = 2");


    // Declare tactics
    DECLARE_VM_BUILTIN(name({"tactic", "arith_normalize"}), tactic_arith_normalize);

    // Register macro
    g_arith_normalizer_macro_name = new name("arith_normalizer");
    g_arith_normalizer_opcode     = new std::string("Arith_Norm");
    register_macro_deserializer(*g_arith_normalizer_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    if (num != 1)
                                        throw corrupted_stream_exception();
                                    return mk_arith_normalizer_macro(args[0]);
                                });

}
void finalize_arith_normalizer() {
    // Delete names for macro
    delete g_arith_normalizer_macro_name;
    delete g_arith_normalizer_opcode;
}

}
