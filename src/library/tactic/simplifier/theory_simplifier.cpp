/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "util/name_hash_map.h"
#include "library/constants.h"
#include "library/util.h"
#include "library/trace.h"
#include "library/num.h"
#include "library/tactic/ac_tactics.h"
#include "library/tactic/simplifier/util.h"
#include "library/tactic/simplifier/theory_simplifier.h"

#ifndef LEAN_DEFAULT_THEORY_SIMPLIFIER_DISTRIBUTE_MUL
#define LEAN_DEFAULT_THEORY_SIMPLIFIER_DISTRIBUTE_MUL true
#endif

namespace lean {

// Dispatch infos
static name_hash_map<theory_simplifier::dispatch_info> * g_dispatch_info_table;




// Theory simplifier
theory_simplifier::theory_simplifier(type_context & tctx): m_tctx(tctx), m_prop_simplifier(tctx), m_arith_simplifier(tctx) {}

bool theory_simplifier::owns(expr const & e) {
    return static_cast<bool>(to_num(e));
}

simp_result theory_simplifier::simplify_binary(expr const & e) {
    return simp_result(e);
}

optional<simp_result> theory_simplifier::simplify_nary(expr const & assoc, expr const & op, buffer<expr> & args) {
    return optional<simp_result>();
}

/*
simp_result theory_simplifier::simplify(expr const & e) {
    expr head = get_app_fn(e);
    if (!is_constant(head))
        return simp_result(e);

    return simp_result(e);

    name id = const_name(head);
    // TODO(dhs): very incomplete
    if (id == get_eq_name()) {
        // TODO(dhs): run arith_simplifier here too
        // result r_arith = m_arith_simplifier.simplify_eq(e);
        // result r_prop = m_prop_simplifier.simplify_eq(r_arith.get_new());
        // return join(r_arith, r_prop);
//        return m_prop_simplifier.simplify_eq(e);
        return simp_result(e);
    // } else if (id == get_iff_name()) {
    //     return m_prop_simplifier.simplify_iff(e);
    // } else if (id == get_not_name()) {
    //     return m_prop_simplifier.simplify_not(e);
    // } else if (id == get_and_name()) {
    //     return m_prop_simplifier.simplify_and(e);
    // } else if (id == get_or_name()) {
    //     return m_prop_simplifier.simplify_or(e);
    } else {
        // auto assoc = is_assoc(m_tctx, e);
        // if (!assoc)
        //     return simp_result(e);
        // auto comm = is_comm(m_tctx, e);
        // if (!comm)
        //     return simp_result(e);
        // buffer<expr> nary_args;
        // auto nary_op = get_app_nary_args(e, nary_args);
        // lean_assert(nary_op);
        // if (!std::is_sorted(nary_args.begin(), nary_args.end())) {
        //     std::sort(nary_args.begin(), nary_args.end());
        //     expr e_new = mk_nary_app(*nary_op, nary_args);
        //     expr pf = perm_ac(m_tctx, *nary_op, *assoc, *comm, e, e_new);
        //     return simp_result(e_new, pf);
        // }
        return simp_result(e);
    }
}
*/
/*
class theory_simplifier {
    enum class dispatch_id {
        EQ,
        // Prop
            AND, OR, NOT, XOR, IMPLIES, ITE,
        // Arith
            LT, GT, LE, GE,
            ADD, MUL,
            NEG, SUB, INV, DIV,
            ZERO, ONE, BIT0, BIT1,
            INT_OF_NAT, RAT_OF_INT, REAL_OF_RAT,
            };

    enum class dispatch_kind { DEFAULT, NARY_ASSOC };

private:
    type_context                 & m_tctx;
    theory_simplifier_options      m_options;

public:
    theory_simplifier(type_context & tctx): m_tctx(tctx), m_options(tctx.get_options()) {}

    optional<pair<dispatch_id, dispatch_kind>> understands_head(name const & head);
    optional<simp_result>                      simplify(dispatch_id did, expr const & prefix, buffer<expr> const & args);
};
*/

void initialize_theory_simplifier() {
    // Dispatch
    // TODO(dhs): add others
    /*
    g_dispatch_info_table = new name_hash_map<theory_simplifier::dispatch_info>({
            {get_eq_name(), theory_simplifier::dispatch_info(theory_simplifier::dispatch_id::EQ, theory_simplifier::dispatch_kind::NARY_ASSOC, 3)}
        });
    */
}

void finalize_theory_simplifier() {
}
}
