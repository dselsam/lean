/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/constants.h"
#include "library/blast/blast.h"
#include "library/blast/proof_expr.h"
#include "library/blast/trace.h"

namespace lean {
namespace blast {

struct by_contradiction_proof_step_cell : public proof_step_cell {
    expr m_href;
    by_contradiction_proof_step_cell(expr const & href): m_href(href) {}
    virtual ~by_contradiction_proof_step_cell() {}
    virtual action_result resolve(expr const & pf) const override {
        expr new_pf = mk_proof_lambda(curr_state(), m_href, pf);
        return action_result::solved(mk_proof_app(get_decidable_by_contradiction_name(), 1, &new_pf));
    }
    virtual bool is_silent() const override { return true; }
};

action_result by_contradiction_action() {
    state &  s  = curr_state();
    expr target = whnf(s.get_target());
    if (!is_prop(target)) return action_result::failed();
    optional<expr> target_decidable = mk_class_instance(mk_app(mk_constant(get_decidable_name()), target));
    if (!target_decidable) return action_result::failed();
    expr href = s.mk_hypothesis(target);
    auto pcell = new by_contradiction_proof_step_cell(href);
    s.push_proof_step(pcell);
    s.set_target(mk_constant(get_false_name()));
    trace_action("by_contradiction");
    return action_result::new_branch();
}
}}
