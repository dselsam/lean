/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "util/sexpr/option_declarations.h"
#include "library/kernel_serializer.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/expr_lt.h"
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

bool is_lt_light_not(expr const & e1, expr const & e2) {
    expr arg1, arg2;
    if (is_explicit_not(e1, arg1)) {
        return is_lt_light_not(arg1, e2);
    } else if (is_explicit_not(e2, arg2)) {
        return !is_lt_light_not(arg2, e1);
    } else {
        return is_lt(e1, e2, true);
    }
}

// Fast simplification
expr fast_simplify_and(buffer<expr> & args) {
    std::sort(args.begin(), args.end(), is_lt_light_not);
    buffer<expr> new_args;
    expr last_lit, curr_lit;
    bool last_lit_pos, curr_lit_pos;

    for (unsigned i = 0; i < args.size(); ++i) {
        if (is_false(args[i])) {
            return mk_false();
        } else if (is_true(args[i])) {
            continue;
        }

        if (is_explicit_not(args[i], curr_lit)) {
            curr_lit_pos = false;
        } else {
            curr_lit = args[i];
            curr_lit_pos = true;
        }

        if (curr_lit == last_lit) {
            if (last_lit_pos != curr_lit_pos) {
                lean_assert(last_lit_pos);
                return mk_false();
            } else {
                continue;
            }
        }

        new_args.push_back(args[i]);
        last_lit = curr_lit;
        last_lit_pos = curr_lit_pos;
    }

    switch (new_args.size()) {
    case 0: return mk_true();
    case 1: return new_args[0];
    default: return mk_left_assoc_app(mk_constant(get_and_name()), new_args);
    }
    lean_unreachable();
}

expr fast_simplify_or(buffer<expr> & args) {
    std::sort(args.begin(), args.end(), is_lt_light_not);
    buffer<expr> new_args;
    expr last_lit, curr_lit;
    bool last_lit_pos, curr_lit_pos;

    for (unsigned i = 0; i < args.size(); ++i) {
        if (is_true(args[i])) {
            return mk_true();
        } else if (is_false(args[i])) {
            continue;
        }

        if (is_explicit_not(args[i], curr_lit)) {
            curr_lit_pos = false;
        } else {
            curr_lit = args[i];
            curr_lit_pos = true;
        }

        if (curr_lit == last_lit) {
            if (last_lit_pos != curr_lit_pos) {
                lean_assert(last_lit_pos);
                return mk_true();
            } else {
                continue;
            }
        }

        new_args.push_back(args[i]);
        last_lit = curr_lit;
        last_lit_pos = curr_lit_pos;
    }

    switch (new_args.size()) {
    case 0: return mk_true();
    case 1: return new_args[0];
    default: return mk_left_assoc_app(mk_constant(get_or_name()), new_args);
    }
    lean_unreachable();
}

// Macro for trusting the fast prop simplifier
static name * g_prop_simplifier_macro_name    = nullptr;
static std::string * g_prop_simplifier_opcode = nullptr;

class prop_simplifier_macro_definition_cell : public macro_definition_cell {
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 1)
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

static expr mk_prop_simplifier_macro(expr const & e, expr const & new_e) {
    macro_definition m(new prop_simplifier_macro_definition_cell());
    expr args[2];
    args[0] = e;
    args[1] = new_e;
    return mk_macro(m, 2, args);
}

// Setup and teardown
void initialize_prop_simplifier() {
    // Options names
    g_prop_simplifier_elim_and   = new name{"prop_simplifier", "elim_and"};

    // Register options
    register_bool_option(*g_prop_simplifier_elim_and, LEAN_DEFAULT_PROP_SIMPLIFIER_ELIM_AND,
                         "(prop_simplifier) (and a b) ==> not (or (not a) (not b))");

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
  // Delete names for macro
    delete g_prop_simplifier_macro_name;
    delete g_prop_simplifier_opcode;
}

// Entry point

/*
simp_result prop_simplify(type_context & tctx, expr const & e) {
    expr new_e = fast_prop_simplify(prop_simplify_options(tctx.get_options()), e);
    expr pf = mk_prop_simplifier_macro(e, new_e);
    return simp_result(new_e, pf);
}
*/
}
