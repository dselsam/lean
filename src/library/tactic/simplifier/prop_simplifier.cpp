/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "util/sexpr/option_declarations.h"
#include "library/kernel_serializer.h"
#include "library/constants.h"
#include "library/util.h"
#include "library/tactic/simplifier/prop_simplifier.h"

#ifndef LEAN_DEFAULT_PROP_SIMPLIFIER_ELIM_AND
#define LEAN_DEFAULT_PROP_SIMPLIFIER_ELIM_AND false
#endif

namespace lean {

// Options
static name * g_prop_simplifier_elim_and = nullptr;

static bool get_prop_simplifier_elim_and(options const & o) {
    return o.get_bool(*g_prop_simplifier_elim_and, LEAN_DEFAULT_PROP_SIMPLIFIER_ELIM_AND);
}

prop_simplifier_options::prop_simplifier_options(options const & o):
    m_elim_and(get_prop_simplifier_elim_and(o)) {}

// Macro for trusting the fast prop simplifier
static name * g_prop_simplifier_macro_name    = nullptr;
static std::string * g_prop_simplifier_opcode = nullptr;

class prop_simplifier_macro_definition_cell : public macro_definition_cell {
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 2)
            throw exception(sstream() << "invalid 'prop_simplifier' macro, incorrect number of arguments");
    }

public:
    prop_simplifier_macro_definition_cell() {}

    virtual name get_name() const { return *g_prop_simplifier_macro_name; }
    virtual expr check_type(expr const & m, abstract_type_context & ctx, bool infer_only) const {
        check_macro(m);
        return mk_app(mk_constant(get_eq_name(), {mk_level_one()}), mk_Prop(), macro_arg(m, 0), macro_arg(m, 1));
    }

    virtual optional<expr> expand(expr const & m, abstract_type_context & ctx) const {
        check_macro(m);
        // TODO(dhs): run slow_prop_simplifier
        return none_expr();
    }

    virtual void write(serializer & s) const {
        s.write_string(*g_prop_simplifier_opcode);
    }

    virtual bool operator==(macro_definition_cell const & other) const {
        if (auto other_ptr = dynamic_cast<prop_simplifier_macro_definition_cell const *>(&other)) {
            return true;
        } else {
            return false;
        }
    }

    virtual unsigned hash() const {
        return get_name().hash();
    }
};

static expr mk_prop_simplifier_macro(expr const & old_e, expr const & new_e) {
    macro_definition m(new prop_simplifier_macro_definition_cell());
    expr args[2];
    args[0] = old_e;
    args[1] = new_e;
    return mk_macro(m, 2, args);
}

simp_result mk_simp_result(expr const & old_e, expr const & new_e) {
    return simp_result(new_e, mk_prop_simplifier_macro(old_e, new_e));
}

// Util
bool is_lt_light_not(expr const & e1, expr const & e2) {
    expr arg1, arg2;
    if (is_not(e1, arg1)) {
        return is_lt_light_not(arg1, e2);
    } else if (is_not(e2, arg2)) {
        return !is_lt_light_not(arg2, e1);
    } else {
        return is_lt(e1, e2, true);
    }
}

// Fast simplification
optional<expr> prop_simplifier::simplify_eq_core(expr const & type, expr const & _lhs, expr const & _rhs) {
    expr lhs = _lhs;
    expr rhs = _rhs;

    if (m_tctx.is_def_eq(lhs, rhs))
        return some_expr(mk_true());

    if (type != mk_Prop())
        return none_expr();

    bool simplified = false;
    expr new_lhs, new_rhs;
    if (is_not(lhs, new_lhs) && is_not(rhs, new_rhs)) {
        lhs = new_lhs;
        rhs = new_rhs;
        simplified = true;
    }

    if (is_true(lhs))
        return some_expr(rhs);

    if (is_false(lhs)) {
        auto r = simplify_not_core(rhs);
        return r ? r : some_expr(mk_app(mk_constant(get_not_name()), rhs));
    }

    if (is_true(rhs))
        return some_expr(lhs);

    if (is_false(rhs)) {
        auto r = simplify_not_core(lhs);
        return r ? r : some_expr(mk_app(mk_constant(get_not_name()), lhs));
    }

    // TODO(dhs): definitional-equality here? Doing structural now for performance reasons.
    if (is_not(lhs, new_lhs) && new_lhs == rhs)
        return some_expr(mk_false());

    if (is_not(rhs, new_rhs) && new_rhs == lhs)
        return some_expr(mk_false());

    if (simplified)
        return some_expr(mk_app(mk_constant(get_eq_name()), type, lhs, rhs));

    return none_expr();
}

optional<expr> prop_simplifier::simplify_not_core(expr const & e) {
    expr arg;
    if (is_not(e, arg)) {
        return some_expr(arg);
    } else if (is_true(e)) {
        return some_expr(mk_false());
    } else if (is_false(e)) {
        return some_expr(mk_true());
    }
    buffer<expr> args;
    expr fn = get_app_args(e, args);
    if (is_constant(fn) && const_name(fn) == get_eq_name() && args.size() == 3 && m_tctx.whnf(args[0]) == mk_Prop()) {
        return some_expr(mk_app(fn, mk_Prop(), mk_app(mk_constant(get_not_name()), args[1]), args[2]));
    }
    return none_expr();
}

optional<expr> prop_simplifier::simplify_and_core(buffer<expr> & args) {
    bool simplified = false;
    if (!std::is_sorted(args.begin(), args.end(), is_lt_light_not)) {
        std::sort(args.begin(), args.end(), is_lt_light_not);
        simplified = true;
    }

    buffer<expr> new_args;
    expr last_lit, curr_lit;
    bool last_lit_pos = false, curr_lit_pos = false;

    for (unsigned i = 0; i < args.size(); ++i) {
        if (is_false(args[i])) {
            return some_expr(mk_false());
        } else if (is_true(args[i])) {
            simplified = true;
            continue;
        }

        if (is_not(args[i], curr_lit)) {
            curr_lit_pos = false;
        } else {
            curr_lit = args[i];
            curr_lit_pos = true;
        }

        // Note use of structural equality
        if (curr_lit == last_lit) {
            if (last_lit_pos != curr_lit_pos) {
                lean_assert(last_lit_pos);
                return some_expr(mk_false());
            } else {
                simplified = true;
                continue;
            }
        }

        new_args.push_back(args[i]);
        last_lit = curr_lit;
        last_lit_pos = curr_lit_pos;
    }

    switch (new_args.size()) {
    case 0: return some_expr(mk_true());
    case 1: return some_expr(new_args[0]);
    default:
        if (simplified)
            return some_expr(mk_nary_app(mk_constant(get_and_name()), new_args));
        else
            return none_expr();
    }
    lean_unreachable();
}

optional<expr> prop_simplifier::simplify_or_core(buffer<expr> & args) {
    bool simplified = false;
    if (!std::is_sorted(args.begin(), args.end(), is_lt_light_not)) {
        std::sort(args.begin(), args.end(), is_lt_light_not);
        simplified = true;
    }

    buffer<expr> new_args;
    expr last_lit, curr_lit;
    bool last_lit_pos = false, curr_lit_pos = false;

    for (unsigned i = 0; i < args.size(); ++i) {
        if (is_true(args[i])) {
            return some_expr(mk_true());
        } else if (is_false(args[i])) {
            simplified = true;
            continue;
        }

        if (is_not(args[i], curr_lit)) {
            curr_lit_pos = false;
        } else {
            curr_lit = args[i];
            curr_lit_pos = true;
        }

        if (curr_lit == last_lit) {
            if (last_lit_pos != curr_lit_pos) {
                lean_assert(last_lit_pos);
                return some_expr(mk_true());
            } else {
                simplified = true;
                continue;
            }
        }

        new_args.push_back(args[i]);
        last_lit = curr_lit;
        last_lit_pos = curr_lit_pos;
    }

    switch (new_args.size()) {
    case 0: return some_expr(mk_true());
    case 1: return some_expr(new_args[0]);
    default:
        if (simplified)
            return some_expr(mk_nary_app(mk_constant(get_or_name()), new_args));
        else
            return none_expr();
    }
    lean_unreachable();
}

// Registered functions
simp_result prop_simplifier::simplify_eq(expr const & e) {
    buffer<expr> args;
    expr op = get_app_args(e, args);
    if (args.size() != 3)
        return simp_result(e);

    if (auto new_e = simplify_eq_core(args[0], args[1], args[2]))
        return mk_simp_result(e, *new_e);
    else
        return simp_result(e);
}

simp_result prop_simplifier::simplify_iff(expr const & e) {
    buffer<expr> args;
    expr op = get_app_args(e, args);
    if (args.size() != 2)
        return simp_result(e);

    if (auto new_e = simplify_eq_core(mk_Prop(), args[0], args[1]))
        return mk_simp_result(e, *new_e);
    else
        return mk_simp_result(e, mk_app(mk_constant(get_eq_name()), mk_Prop(), args[0], args[1]));
}

simp_result prop_simplifier::simplify_not(expr const & e) {
    buffer<expr> args;
    expr op = get_app_args(e, args);
    if (args.size() != 1)
        return simp_result(e);

    if (auto new_e = simplify_not_core(args[0]))
        return mk_simp_result(e, *new_e);
    else
        return simp_result(e);
}

simp_result prop_simplifier::simplify_and(expr const & e) {
    throw exception("NYI");
    return simp_result(e);
    // buffer<expr> args;
    // expr op = get_app_args(e, args);
    // if (args.size() != 2)
    //     return simp_result(e);

    // buffer<expr> nary_args;
    // optional<expr> nary_op = get_app_nary_args(e, nary_args);
    // lean_assert(nary_op && *nary_op == op);
    // if (auto new_e = simplify_and_core(nary_args))
    //     return mk_simp_result(e, *new_e);
    // else
    //     return simp_result(e);
}

simp_result prop_simplifier::simplify_or(expr const & e) {
    throw exception("NYI");
    return simp_result(e);
    // buffer<expr> args;
    // expr op = get_app_args(e, args);
    // if (args.size() != 2)
    //     return simp_result(e);

    // buffer<expr> nary_args;
    // optional<expr> nary_op = get_app_nary_args(e, nary_args);
    // lean_assert(nary_op && *nary_op == op);
    // if (auto new_e = simplify_or_core(nary_args))
    //     return mk_simp_result(e, *new_e);
    // else
    //     return simp_result(e);
}

// Setup and teardown
void initialize_prop_simplifier() {
    // Option names
    g_prop_simplifier_elim_and     = new name{"prop_simplifier", "elim_and"};

    // Register options
    register_bool_option(*g_prop_simplifier_elim_and, LEAN_DEFAULT_PROP_SIMPLIFIER_ELIM_AND,
                         "(prop_simplifier) (and a b c) ==> (not (or (not a) (not b) (not c)))");

    // Register macro
    g_prop_simplifier_macro_name = new name("prop_simplifier");
    g_prop_simplifier_opcode     = new std::string("Prop_Simp");
    register_macro_deserializer(*g_prop_simplifier_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    if (num != 2)
                                        throw corrupted_stream_exception();
                                    return mk_prop_simplifier_macro(args[0], args[1]);
                                });
}

void finalize_prop_simplifier() {
    // Option names
    delete g_prop_simplifier_elim_and;

    // Macro names
    delete g_prop_simplifier_macro_name;
    delete g_prop_simplifier_opcode;
}

}
