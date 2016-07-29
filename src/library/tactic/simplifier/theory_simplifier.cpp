/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "util/name_hash_map.h"
#include "library/constants.h"
#include "library/tactic/simplifier/theory_simplifier.h"

#ifndef LEAN_DEFAULT_THEORY_SIMPLIFIER_DISTRIBUTE_MUL
#define LEAN_DEFAULT_THEORY_SIMPLIFIER_DISTRIBUTE_MUL true
#endif

namespace lean {

//using theory_simplifier::dispatch_id;
//using theory_simplifier::dispatch_kind;
//using theory_simplifier::dispatch_info;

// Dispatch infos
static name_hash_map<theory_simplifier::dispatch_info> * g_dispatch_info_table;




// Theory simplifier
theory_simplifier::theory_simplifier(type_context & tctx): m_tctx(tctx), m_prop_simplifier(tctx), m_arith_simplifier(tctx) {}


optional<theory_simplifier::dispatch_info> theory_simplifier::understands_head(name const & head) {
    auto it = g_dispatch_info_table->find(head);
    if (it != g_dispatch_info_table->end()) {
        return optional<dispatch_info>(it->second);
    } else {
        return optional<dispatch_info>();
    }
}

optional<simp_result> theory_simplifier::simplify(theory_simplifier::dispatch_id did, expr const & prefix, buffer<expr> const & args) {
    throw exception("NYI");
    switch (did) {
    case theory_simplifier::dispatch_id::EQ:   return simplify_eq(prefix, args);
    default:                return optional<simp_result>();
    }
    lean_unreachable();
}


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
    g_dispatch_info_table = new name_hash_map<theory_simplifier::dispatch_info>({
            {get_eq_name(), theory_simplifier::dispatch_info(theory_simplifier::dispatch_id::EQ, theory_simplifier::dispatch_kind::NARY_ASSOC, 3)}
        });
}

void finalize_theory_simplifier() {
}
}
