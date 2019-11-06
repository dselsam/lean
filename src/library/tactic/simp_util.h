/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#define lean_simp_trace(CTX, N, CODE) lean_trace(N, scope_trace_env _scope1(CTX.env(), CTX); CODE)
#define lean_simp_trace_d(CTX, N, CODE) lean_trace_d(N, scope_trace_env _scope1(CTX.env(), CTX); CODE)

namespace lean {
template<typename Prover>
class instantiate_emetas_fn {
    Prover & m_prover;

    // TODO(Leo): move to a different module?
    optional<expr> try_auto_param(type_context_old & ctx, expr const & type) {
        optional<expr_pair> p = is_auto_param(type);
        if (!p) return none_expr();
        optional<name> c = name_lit_to_name(p->second);
        if (!c) return none_expr();
        optional<declaration> d = ctx.env().find(*c);
        if (!d) return none_expr();
        if (!ctx.is_def_eq(d->get_type(), mk_tactic_unit())) return none_expr();

        vm_obj tac = get_vm_state().get_constant(*c);
        tactic_state s  = mk_tactic_state_for(ctx.env(), ctx.get_options(), name("_simp_auto_param"), ctx.lctx(), p->first);
        vm_obj r_obj    = invoke(tac, to_obj(s));
        optional<tactic_state> s_new = tactic::is_success(r_obj);
        if (!s_new || s_new->goals()) return none_expr();
        metavar_context mctx   = s_new->mctx();
        expr result            = mctx.instantiate_mvars(s_new->main());
        if (has_expr_metavar(result)) return none_expr();
        ctx.set_mctx(mctx);
        return some_expr(result);
    }

public:
    instantiate_emetas_fn(Prover & prover):
        m_prover(prover) {}

    bool operator()(type_context_old & ctx, list<expr> const & emetas, list<bool> const & instances) {
        bool failed = false;
        for_each2(emetas, instances, [&](expr const & mvar, bool const & is_instance) {
                if (failed) return;
                expr mvar_type = ctx.instantiate_mvars(ctx.infer(mvar));
                if (has_idx_metavar(mvar_type)) {
                    failed = true;
                    return;
                }

                if (ctx.is_assigned(mvar)) return;

                if (is_instance) {
                    if (auto v = ctx.mk_class_instance(mvar_type)) {
                        if (!ctx.is_def_eq(mvar, *v)) {
                            lean_simp_trace(ctx, name({"simplify", "failure"}),
                                            tout() << "unable to assign instance for: " << mvar_type << "\n";);
                            failed = true;
                            return;
                        }
                    } else {
                        lean_simp_trace(ctx, name({"simplify", "failure"}),
                                        tout() << "unable to synthesize instance for: " << mvar_type << "\n";);
                        failed = true;
                        return;
                    }
                }

                if (ctx.is_assigned(mvar)) return;

                if (optional<expr> pf = try_auto_param(ctx, mvar_type)) {
                    lean_verify(ctx.is_def_eq(mvar, *pf));
                    return;
                }

                if (ctx.is_prop(mvar_type)) {
                    if (auto pf = m_prover(mvar_type)) {
                        lean_verify(ctx.is_def_eq(mvar, *pf));
                        return;
                    } else {
                        lean_simp_trace(ctx, name({"simplify", "failure"}),
                                        tout() << "failed to prove: " << mvar << " : " << mvar_type << "\n";);
                        failed = true;
                        return;
                    }
                } else {
                    lean_simp_trace(ctx, name({"simplify", "failure"}),
                                    tout() << "failed to assign: " << mvar << " : " << mvar_type << "\n";);
                    failed = true;
                    return;
                }
            });
        return !failed;
    }
};
}
