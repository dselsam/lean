/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include <functional>
#include <iostream>
#include "util/flet.h"
#include "util/freset.h"
#include "util/pair.h"
#include "util/optional.h"
#include "util/interrupt.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/abstract.h"
#include "kernel/expr_maps.h"
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/normalize.h"
#include "library/expr_lt.h"
#include "library/num.h"
#include "library/util.h"
#include "library/norm_num.h"
#include "library/attribute_manager.h"
#include "library/defeq_canonizer.h"
#include "library/class_instance_resolution.h"
#include "library/relation_manager.h"
#include "library/app_builder.h"
#include "library/congr_lemma.h"
#include "library/fun_info.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_name.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/ac_tactics.h"
#include "library/tactic/app_builder_tactics.h"
#include "library/tactic/simplifier/simplifier.h"
#include "library/tactic/simplifier/simp_lemmas.h"
#include "library/tactic/simplifier/simp_extensions.h"
#include "library/tactic/simplifier/theory_simplifier.h"
#include "library/tactic/simplifier/ceqv.h"
#include "library/tactic/simplifier/util.h"

#ifndef LEAN_DEFAULT_SIMPLIFY_MAX_STEPS
#define LEAN_DEFAULT_SIMPLIFY_MAX_STEPS 1000
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_MAX_REWRITES
#define LEAN_DEFAULT_SIMPLIFY_MAX_REWRITES 5000
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_REWRITE_AC
#define LEAN_DEFAULT_SIMPLIFY_REWRITE_AC false
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_MEMOIZE
#define LEAN_DEFAULT_SIMPLIFY_MEMOIZE true
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_CONTEXTUAL
#define LEAN_DEFAULT_SIMPLIFY_CONTEXTUAL true
#endif
#ifndef LEAN_DEFAULT_SIMPLIFY_LIFT_EQ
#define LEAN_DEFAULT_SIMPLIFY_LIFT_EQ false
#endif
#ifndef LEAN_DEFAULT_DEFEQ_SIMPLIFY_CANONIZE_PROOFS
#define LEAN_DEFAULT_DEFEQ_SIMPLIFY_CANONIZE_PROOFS false
#endif

namespace lean {

/* Options */

static name * g_simplify_max_steps            = nullptr;
static name * g_simplify_max_rewrites         = nullptr;
static name * g_simplify_rewrite_ac           = nullptr;
static name * g_simplify_memoize              = nullptr;
static name * g_simplify_contextual           = nullptr;
static name * g_simplify_lift_eq              = nullptr;
static name * g_simplify_canonize_proofs      = nullptr;

static unsigned get_simplify_max_steps(options const & o) {
    return o.get_unsigned(*g_simplify_max_steps, LEAN_DEFAULT_SIMPLIFY_MAX_STEPS);
}

static unsigned get_simplify_max_rewrites(options const & o) {
    return o.get_unsigned(*g_simplify_max_rewrites, LEAN_DEFAULT_SIMPLIFY_MAX_REWRITES);
}

static bool get_simplify_rewrite_ac(options const & o) {
    return o.get_bool(*g_simplify_rewrite_ac, LEAN_DEFAULT_SIMPLIFY_REWRITE_AC);
}

static bool get_simplify_memoize(options const & o) {
    return o.get_bool(*g_simplify_memoize, LEAN_DEFAULT_SIMPLIFY_MEMOIZE);
}

static bool get_simplify_contextual(options const & o) {
    return o.get_bool(*g_simplify_contextual, LEAN_DEFAULT_SIMPLIFY_CONTEXTUAL);
}

static bool get_simplify_lift_eq(options const & o) {
    return o.get_bool(*g_simplify_lift_eq, LEAN_DEFAULT_SIMPLIFY_LIFT_EQ);
}

static bool get_simplify_canonize_proofs(options const & o) {
    return o.get_bool(*g_simplify_canonize_proofs, LEAN_DEFAULT_DEFEQ_SIMPLIFY_CANONIZE_PROOFS);
}

#define lean_simp_trace(tctx, n, code) lean_trace(n, scope_trace_env _scope1(tctx.env(), tctx); code)

/* Util (move to util.h?) */


/* Main simplifier class */

class simplifier {
    type_context              m_tctx;
    theory_simplifier         m_theory_simplifier;

    name                      m_rel;

    simp_lemmas               m_slss;
    simp_lemmas               m_ctx_slss;

    optional<expr>            m_curr_nary_op;

    vm_obj const &            m_prove_fn;

    /* Logging */
    unsigned                  m_num_steps{0};
    unsigned                  m_num_rewrites{0};

    bool                      m_need_restart{false};

    /* Options */
    unsigned                  m_max_steps;
    unsigned                  m_max_rewrites;
    bool                      m_rewrite_ac;
    bool                      m_memoize;
    bool                      m_contextual;
    bool                      m_lift_eq;
    bool                      m_canonize_proofs;

    /* Cache */
    struct key {
        name              m_rel;
        expr              m_e;
        unsigned          m_hash;

        key(name const & rel, expr const & e):
            m_rel(rel), m_e(e), m_hash(hash(rel.hash(), e.hash())) { }
    };

    struct key_hash_fn {
        unsigned operator()(key const & k) const { return k.m_hash; }
    };

    struct key_eq_fn {
        bool operator()(key const & k1, key const & k2) const {
            return k1.m_rel == k2.m_rel && k1.m_e == k2.m_e;
        }
    };

    typedef std::unordered_map<key, simp_result, key_hash_fn, key_eq_fn> simplify_cache;
    simplify_cache m_cache;
    optional<simp_result> cache_lookup(expr const & e);
    void cache_save(expr const & e, simp_result const & r);

    /* Basic helpers */
    environment const & env() const { return m_tctx.env(); }

    simp_result join(simp_result const & r1, simp_result const & r2) { return ::lean::join(m_tctx, m_rel, r1, r2); }

    bool using_eq() { return m_rel == get_eq_name(); }

    bool is_dependent_fn(expr const & f) {
        expr f_type = m_tctx.whnf(m_tctx.infer(f));
        lean_assert(is_pi(f_type));
        return has_free_vars(binding_body(f_type));
    }

    simp_lemmas add_to_slss(simp_lemmas const & _slss, buffer<expr> const & ls) {
        simp_lemmas slss = _slss;
        for (unsigned i = 0; i < ls.size(); i++) {
            expr const & l = ls[i];
            try {
                // TODO(Leo,Daniel): should we allow the user to set the priority of local lemmas?
                slss = add(m_tctx, slss, mlocal_name(l), m_tctx.infer(l), l, LEAN_DEFAULT_PRIORITY);
            } catch (exception e) {
            }
        }
        return slss;
    }

    bool instantiate_emetas(tmp_type_context & tmp_tctx, unsigned num_emeta, list<expr> const & emetas, list<bool> const & instances);

    /* Simp_Results */
    simp_result lift_from_eq(expr const & e_old, simp_result const & r_eq);

    /* N-ary */
    void simplify_nary_args(expr const & op, expr const & arg, buffer<expr> & nary_args, buffer<simp_result> & nary_results, bool has_simplified = false);

    /* Simplification */
    simp_result simplify(expr const & e);

    /* Simplying the necessary subterms */
    simp_result simplify_subterms_lambda(expr const & e);
    simp_result simplify_subterms_pi(expr const & e);
    simp_result simplify_subterms_app(expr const & e);

    /* Called from simplify_subterms_app */
    simp_result simplify_operator_of_app(expr const & e);
    simp_result simplify_subterms_app_nary(expr const & assoc, expr const & e);
    simp_result simplify_each_nary_arg(expr const & op, expr const & e);


    /* Extenisons */
    simp_result simplify_user_extensions(expr const & e);

    /* Proving */
    optional<expr> prove(expr const & thm);

    /* Rewriting */
    simp_result rewrite(expr const & e, simp_lemmas const & slss);
    simp_result rewrite(expr const & e, list<simp_lemma> const & lemmas);

    simp_result rewrite_a(expr const & assoc, expr const & e, simp_lemma const & lemma);
    optional<simp_result> rewrite_a(buffer<expr> const & nary_args, buffer<expr> const & nary_pattern_args, unsigned offset, simp_lemma const & sl);

    simp_result rewrite_ac(expr const & assoc, expr const & comm, expr const & e, simp_lemma const & lemma);
    simp_result rewrite(expr const & e, simp_lemma const & lemma);

    /* Canonicalize */
    expr canonize_args(expr const & e);

    /* Congruence */
    simp_result congr_fun_arg(simp_result const & r_f, simp_result const & r_arg);
    simp_result congr(simp_result const & r_f, simp_result const & r_arg);
    simp_result congr_fun(simp_result const & r_f, expr const & arg);
    simp_result congr_arg(expr const & f, simp_result const & r_arg);
    simp_result congr_funs(simp_result const & r_f, buffer<expr> const & args);

    simp_result try_congrs(expr const & e);
    simp_result try_congr(expr const & e, user_congr_lemma const & cr);

    template<typename F>
    optional<simp_result> synth_congr(expr const & e, F && simp);

    expr remove_unnecessary_casts(expr const & e);

    /* Apply whnf and eta-reduction
       \remark We want (Sum n (fun x, f x)) and (Sum n f) to be the same.
       \remark We may want to switch to eta-expansion later (see paper: "The Virtues of Eta-expansion").
       TODO(Daniel, Leo): should we add an option for disabling/enabling eta? */
    expr whnf_eta(expr const & e);

public:
    simplifier(type_context & tctx, name const & rel, simp_lemmas const & slss, vm_obj const & prove_fn):
        m_tctx(tctx), m_theory_simplifier(tctx), m_rel(rel), m_slss(slss), m_prove_fn(prove_fn),
        /* Options */
        m_max_steps(get_simplify_max_steps(tctx.get_options())),
        m_max_rewrites(get_simplify_max_rewrites(tctx.get_options())),
        m_rewrite_ac(get_simplify_rewrite_ac(tctx.get_options())),
        m_memoize(get_simplify_memoize(tctx.get_options())),
        m_contextual(get_simplify_contextual(tctx.get_options())),
        m_lift_eq(get_simplify_lift_eq(tctx.get_options())),
        m_canonize_proofs(get_simplify_canonize_proofs(tctx.get_options()))
        { }

    simp_result operator()(expr const & e)  {
        scope_trace_env scope(env(), m_tctx);
        simp_result r(e);
        while (true) {
            m_need_restart = false;
            r = join(r, simplify(r.get_new()));
            if (!m_need_restart)
                return r;
            m_cache.clear();
        }
    }
};

/* Cache */

optional<simp_result> simplifier::cache_lookup(expr const & e) {
    auto it = m_cache.find(key(m_rel, e));
    if (it == m_cache.end()) return optional<simp_result>();
    return optional<simp_result>(it->second);
}

void simplifier::cache_save(expr const & e, simp_result const & r) {
    m_cache.insert(mk_pair(key(m_rel, e), r));
}

/* Simp_Results */

simp_result simplifier::lift_from_eq(expr const & e_old, simp_result const & r_eq) {
    if (!r_eq.has_proof()) return r_eq;
    lean_assert(r_eq.has_proof());
    /* r_eq.get_proof() : e_old = r_eq.get_new() */
    /* goal : e_old <m_rel> r_eq.get_new() */
    type_context::tmp_locals local_factory(m_tctx);
    expr local = local_factory.push_local(name(), m_tctx.infer(e_old));
    expr motive_local = mk_app(m_tctx, m_rel, e_old, local);
    /* motive = fun y, e_old <m_rel> y */
    expr motive = local_factory.mk_lambda(motive_local);
    /* Rxx = x <m_rel> x */
    expr Rxx = mk_refl(m_tctx, m_rel, e_old);
    expr pf = mk_eq_rec(m_tctx, motive, Rxx, r_eq.get_proof());
    return simp_result(r_eq.get_new(), pf);
}

/* Whnf + Eta */
expr simplifier::whnf_eta(expr const & e) {
    return try_eta(m_tctx.whnf(e));
}

/* Simplification */

simp_result simplifier::simplify(expr const & e) {
    m_num_steps++;
    lean_trace_inc_depth("simplifier");
    lean_trace_d("simplifier", tout() << m_rel << ": " << e << "\n";);

    if (m_num_steps > m_max_steps)
        throw exception("simplifier failed, maximum number of steps exceeded");

    if (m_memoize) {
        if (auto it = cache_lookup(e)) return *it;
    }

    simp_result r(whnf_eta(e));

    // [1] Simplify subterms using congruence
    switch (r.get_new().kind()) {
    case expr_kind::Local:
    case expr_kind::Meta:
    case expr_kind::Sort:
    case expr_kind::Constant:
        // no-op
        break;
    case expr_kind::Var:
        lean_unreachable();
    case expr_kind::Macro:
        break;
    case expr_kind::Lambda:
        if (using_eq()) r = join(r, simplify_subterms_lambda(r.get_new()));
        break;
    case expr_kind::Pi:
        r = join(r, simplify_subterms_pi(r.get_new()));
        break;
    case expr_kind::App:
        r = join(r, simplify_subterms_app(r.get_new()));
        break;
    case expr_kind::Let:
        // whnf unfolds let-expressions
        lean_unreachable();
    }

    r.update(whnf_eta(r.get_new()));

    // Suppose we start with: [(a + d)] and [a] ==> [b + c]
    // We want to simplify the arguments [b] and [c], but we do not want to trigger any of the n-ary processing to come.
    // We also do not want to cache the result, since [b + c] ==> [b' + c'] might not always be correct, depending on [b'] and [c'].
    // So we return here without caching.
    if (using_eq() && m_curr_nary_op && m_curr_nary_op == get_binary_op(r.get_new()))
        return r;

    // [2] Simplify with the theory simplifier
    // TODO(dhs): should the theory simplifier be last?
    if (is_app(r.get_new())) {
        if (using_eq()) {
            simp_result r_theory = m_theory_simplifier.simplify(r.get_new());
            lean_trace_d(name({"simplifier", "theory"}), tout() << r.get_new() << " ==> " << r_theory.get_new() << "\n";);
            r = join(r, r_theory);
            r.update(whnf_eta(r.get_new()));
        }
    }

    // Note: the theory simplifier guarantees that no new subterms are introduced that need to be simplified.
    // Thus we never need to repeat unless something is simplified downstream of here.

    // [3] user simplifier extensions
    if (is_app(r.get_new())) {
        r.update(whnf_eta(r.get_new()));
        simp_result r_user = simplify_user_extensions(r.get_new());
        if (r_user.get_new() != r.get_new()) {
            r = join(r, r_user);
            if (using_eq()) {
                // only need to repeat here if the theory simplifier might trigger
                r = join(r, simplify(r.get_new()));
                r.update(whnf_eta(r.get_new()));
            }
        }
    }

    // [4] rewriting
    simp_lemmas all_slss = ::lean::join(m_slss, m_ctx_slss);
    simp_result r_rewrite = rewrite(r.get_new(), all_slss);
    if (r_rewrite.get_new() != r.get_new()) {
        r = join(r, r_rewrite);
        r = join(r, simplify(r.get_new()));
        r.update(whnf_eta(r.get_new()));
    }

    // [5] lifting
    if (m_lift_eq && !using_eq()) {
        simp_result r_eq;
        {
            flet<name> use_eq(m_rel, get_eq_name());
            r_eq = simplify(r.get_new());
        }
        if (r_eq.get_new() != r.get_new()) {
            r = join(r, lift_from_eq(r.get_new(), r_eq));
            r = join(r, simplify(r.get_new()));
        }
    }

    if (m_memoize) cache_save(e, r);
    return r;
}

simp_result simplifier::simplify_subterms_lambda(expr const & e) {
    lean_assert(is_lambda(e));
    expr t = e;

    type_context::tmp_locals local_factory(m_tctx);

    expr l = local_factory.push_local_from_binding(t);
    t = instantiate(binding_body(t), l);

    simp_result r = simplify(t);
    expr new_t = local_factory.mk_lambda(r.get_new());

    if (r.has_proof()) {
        expr lam_pf = local_factory.mk_lambda(r.get_proof());
        expr funext_pf = mk_app(m_tctx, get_funext_name(), lam_pf);
        return simp_result(new_t, funext_pf);
    } else {
        return simp_result(new_t);
    }
}

simp_result simplifier::simplify_subterms_pi(expr const & e) {
    lean_assert(is_pi(e));
    return try_congrs(e);
}

expr simplifier::canonize_args(expr const & e) {
        buffer<expr> args;
        bool modified = false;
        expr f        = get_app_args(e, args);
        fun_info info = get_fun_info(m_tctx, f, args.size());
        unsigned i    = 0;
        for (param_info const & pinfo : info.get_params_info()) {
            lean_assert(i < args.size());
            expr new_a;
            if (pinfo.is_inst_implicit() || (m_canonize_proofs && pinfo.is_prop())) {
                new_a = ::lean::defeq_canonize(m_tctx, args[i], m_need_restart);
                lean_trace(name({"simplifier", "canonize"}),
                           tout() << "\n" << args[i] << "\n===>\n" << new_a << "\n";);
                if (new_a != args[i]) {
                    modified = true;
                    args[i] = new_a;
                }
            }
            i++;
        }

        if (!modified)
            return e;
        else
            return mk_app(f, args);
}

simp_result simplifier::simplify_operator_of_app(expr const & e) {
    lean_assert(is_app(e));
    buffer<expr> args;
    expr const & f = get_app_args(e, args);
    simp_result r_f = simplify(f);
    return congr_funs(r_f, args);
}

simp_result simplifier::simplify_each_nary_arg(expr const & op, expr const & e) {
    expr arg1, arg2;
    if (is_binary_app_of(e, op, arg1, arg2)) {
        simp_result r1 = simplify_each_nary_arg(op, arg1);
        simp_result r2 = simplify_each_nary_arg(op, arg2);
        expr new_e = mk_app(op, r1.get_new(), r2.get_new());
        if (r1.has_proof() && r2.has_proof()) {
            return simp_result(new_e, mk_congr_arg_bin(m_tctx, op, r1.get_proof(), r2.get_proof()));
        } else if (r1.has_proof()) {
            return simp_result(new_e, mk_congr_arg_bin_fst(m_tctx, op, r1.get_proof(), r2.get_new()));
        } else if (r2.has_proof()) {
            return simp_result(new_e, mk_congr_arg(m_tctx, mk_app(op, r1.get_new()), r2.get_proof()));
        } else {
            return simp_result(new_e);
        }
    } else {
        return simplify(e);
    }
}

simp_result simplifier::simplify_subterms_app_nary(expr const & assoc, expr const & e) {
    expr op = app_fn(app_fn(e));
    flet<optional<expr>> with_nary_assoc(m_curr_nary_op, some_expr(op));
    simp_result r_congr = simplify_each_nary_arg(op, e);
    simp_result r_flat  = simp_result(flat_assoc(m_tctx, op, assoc, r_congr.get_new()));
    return join(r_congr, r_flat);
}

simp_result simplifier::simplify_subterms_app(expr const & _e) {
    lean_assert(is_app(_e));
    if (m_theory_simplifier.owns(_e))
        return simp_result(_e);

    expr e = canonize_args(_e);

    if (optional<expr> assoc = is_assoc(m_tctx, e))
        return simplify_subterms_app_nary(*assoc, e);

    // (1) Try user-defined congruences
    simp_result r_user = try_congrs(e);
    if (r_user.has_proof()) {
        if (using_eq()) return join(r_user, simplify_operator_of_app(r_user.get_new()));
        else return r_user;
    }

    // (2) Synthesize congruence lemma
    if (using_eq()) {
        optional<simp_result> r_args = synth_congr(e, [&](expr const & e) {
                return simplify(e);
            });
        if (r_args) return join(*r_args, simplify_operator_of_app(r_args->get_new()));
    }
    // (3) Fall back on generic binary congruence
    if (using_eq()) {
        expr const & f = app_fn(e);
        expr const & arg = app_arg(e);

        simp_result r_f = simplify(f);

        if (is_dependent_fn(f)) {
            if (r_f.has_proof()) return congr_fun(r_f, arg);
            else return mk_app(r_f.get_new(), arg);
        } else {
            simp_result r_arg = simplify(arg);
            return congr_fun_arg(r_f, r_arg);
        }
    }
    return simp_result(e);
}

/* Extensions */
simp_result simplifier::simplify_user_extensions(expr const & _e) {
    simp_result r(_e);
    expr op = get_app_fn(_e);
    if (!is_constant(op)) return simp_result(_e);
    name head = const_name(op);
    buffer<unsigned> ext_ids;
    get_simp_extensions_for(m_tctx.env(), head, ext_ids);
    for (unsigned ext_id : ext_ids) {
        expr e = r.get_new();
        expr e_type = m_tctx.infer(e);
        metavar_context mctx = m_tctx.mctx();
        expr result_mvar = mctx.mk_metavar_decl(m_tctx.lctx(), e_type);
        m_tctx.set_mctx(mctx); // the app-builder needs to know about these metavars
        expr goal_type = mk_app(m_tctx, m_rel, e, result_mvar);
        expr goal_mvar = mctx.mk_metavar_decl(m_tctx.lctx(), goal_type);
        vm_obj s = to_obj(tactic_state(m_tctx.env(), m_tctx.get_options(), mctx, list<expr>(goal_mvar), goal_mvar));
        vm_obj simp_ext_result = get_tactic_vm_state(m_tctx.env()).invoke(ext_id, 1, &s);
        optional<tactic_state> s_new = is_tactic_success(simp_ext_result);
        if (s_new) {
            m_tctx.set_mctx(s_new->mctx());
            expr result = m_tctx.instantiate_mvars(result_mvar);
            expr proof = m_tctx.instantiate_mvars(goal_mvar);
            lean_trace(name({"simplifier", "user_extensions"}),
                       tout() << proof << " : " << e << " [" << m_rel << "] " << result << "\n";);
            if (is_app_of(proof, get_eq_refl_name(), 2) || is_app_of(proof, get_rfl_name(), 2)) {
                r.update(result);
            } else {
                r = join(r, simp_result(result, proof));
            }
        } else {
            lean_trace(name({"simplifier", "extensions"}),
                       tout() << "extension failed on goal " << goal_type << "\n";);
        }
    }
    return r;
}

/* Proving */

optional<expr> simplifier::prove(expr const & goal) {
    metavar_context mctx = m_tctx.mctx();
    expr goal_mvar = mctx.mk_metavar_decl(m_tctx.lctx(), goal);
    lean_trace(name({"simplifier", "prove"}), tout() << goal_mvar << " : " << goal << "\n";);
    vm_obj s = to_obj(tactic_state(m_tctx.env(), m_tctx.get_options(), mctx, list<expr>(goal_mvar), goal_mvar));
    vm_obj prove_fn_result = get_tactic_vm_state(m_tctx.env()).invoke(m_prove_fn, s);
    optional<tactic_state> s_new = is_tactic_success(prove_fn_result);
    if (s_new) {
        m_tctx.set_mctx(s_new->mctx());
        expr proof = m_tctx.instantiate_mvars(goal_mvar);
        lean_trace(name({"simplifier", "prove"}), tout() << "SUCCESS: " << proof << " : " << m_tctx.infer(proof) << "\n";);
        return some_expr(proof);
    } else {
        lean_trace(name({"simplifier", "prove"}), tout() << "prove_fn failed to prove " << goal << "\n";);
        return none_expr();
    }
}

/* Rewriting */
simp_result simplifier::rewrite(expr const & e, simp_lemmas const & slss) {
    simp_lemmas_for const * sr = slss.find(m_rel);
    if (!sr) return simp_result(e);

    list<simp_lemma> const * srs = sr->find_simp(e);
    if (!srs) {
        lean_trace(name({"debug", "simplifier", "try_rewrite"}), tout() << "no simp lemmas for: " << e << "\n";);
        return simp_result(e);
    }

    return rewrite(e, *srs);
}

simp_result simplifier::rewrite(expr const & e, list<simp_lemma> const & lemmas) {
    auto assoc = !using_eq() ? none_expr() : is_assoc(m_tctx, e);
    auto comm  = !using_eq() ? none_expr() : is_comm(m_tctx, e);

    for (simp_lemma const & lemma : lemmas) {
        simp_result r;
        if (assoc && comm)
            r = rewrite_ac(*assoc, *comm, e, lemma);
        else if (assoc)
            r = rewrite_a(*assoc, e, lemma);
        else
            r = rewrite(e, lemma);
        if (r.has_proof())
            return r;
    }
    return simp_result(e);
}

simp_result simplifier::rewrite_a(expr const & assoc, expr const & e, simp_lemma const & sl) {
    buffer<expr> nary_args;
    optional<expr> nary_op = get_app_nary_args(e, nary_args);
    lean_assert(nary_op);

    buffer<expr> nary_pattern_args;
    optional<expr> nary_pattern_op = get_app_nary_args(sl.get_lhs(), nary_pattern_args);
    lean_assert(nary_pattern_op);

    if (m_tctx.is_def_eq(*nary_op, *nary_pattern_op))
        return simp_result(e);

    unsigned num_patterns = nary_pattern_args.size();

    if (nary_args.size() < num_patterns)
        return simp_result(e);

    for (unsigned i = 0; i <= nary_args.size() - num_patterns; ++i) {
        if (optional<simp_result> r = rewrite_a(nary_args, nary_pattern_args, i, sl)) {
            lean_assert(r->has_proof());
            unsigned j = nary_args.size() - 1;
            expr e_new = (j >= i + num_patterns) ? nary_args[j] : r->get_new();
            j = (j >= i + num_patterns) ? (j - 1) : (j - num_patterns);
            while (j + 1 > 0) {
                if (j >= i + num_patterns || j < i) {
                    e_new = mk_app(*nary_op, nary_args[j], e_new);
                    j -= 1;
                } else {
                    e_new = mk_app(*nary_op, r->get_new(), e_new);
                    j -= num_patterns;
                }
            }
            lean_trace(name({"simplifier", "rewrite", "assoc"}), tout() << e << " ==> " << e_new << "\n";);
            return simp_result(e_new, mk_rewrite_assoc_macro(assoc, mk_eq(m_tctx, e, e_new), r->get_proof()));
        }
    }
    return simp_result(e);
}

optional<simp_result> simplifier::rewrite_a(buffer<expr> const & nary_args, buffer<expr> const & nary_pattern_args, unsigned offset, simp_lemma const & sl) {
    unsigned num_patterns = nary_pattern_args.size();
    tmp_type_context tmp_tctx(m_tctx, sl.get_num_umeta(), sl.get_num_emeta());
    for (unsigned i = 0; i < num_patterns; ++i) {
        if (!m_tctx.is_def_eq(nary_args[offset+i], nary_pattern_args[i]))
            return optional<simp_result>();
    }

    if (!instantiate_emetas(tmp_tctx, sl.get_num_emeta(), sl.get_emetas(), sl.get_instances()))
        return optional<simp_result>();

    for (unsigned i = 0; i < sl.get_num_umeta(); i++) {
        if (!tmp_tctx.is_uassigned(i))
            return optional<simp_result>();
    }

    expr new_lhs = tmp_tctx.instantiate_mvars(sl.get_lhs());
    expr new_rhs = tmp_tctx.instantiate_mvars(sl.get_rhs());

    expr pf = tmp_tctx.instantiate_mvars(sl.get_proof());
    return optional<simp_result>(simp_result(new_rhs, pf));
}

simp_result simplifier::rewrite_ac(expr const & assoc, expr const & comm, expr const & e, simp_lemma const & sl) {
    buffer<expr> nary_args;
    optional<expr> nary_op = get_app_nary_args(e, nary_args);
    lean_assert(nary_op);

    buffer<expr> nary_pattern_args;
    optional<expr> nary_pattern_op = get_app_nary_args(sl.get_lhs(), nary_pattern_args);
    lean_assert(nary_pattern_op);
    lean_assert(m_tctx.is_def_eq(*nary_op, *nary_pattern_op));

    unsigned num_patterns = nary_pattern_args.size();

    if (nary_args.size() < num_patterns)
        return simp_result(e);

    lean_trace(name({"simplifier", "rewrite", "ac"}), tout() << "(not yet implemented)" << "\n";);
    return rewrite_a(assoc, e, sl);
}

simp_result simplifier::rewrite(expr const & e, simp_lemma const & sl) {
    tmp_type_context tmp_tctx(m_tctx, sl.get_num_umeta(), sl.get_num_emeta());
    lean_simp_trace(tmp_tctx, name({"debug", "simplifier", "try_rewrite"}), tout() << e << " =?= " << sl.get_lhs() << "\n";);

    if (!tmp_tctx.is_def_eq(e, sl.get_lhs())) return simp_result(e);

    lean_simp_trace(tmp_tctx, name({"simplifier", "rewrite"}),
                    expr new_lhs = tmp_tctx.instantiate_mvars(sl.get_lhs());
                    expr new_rhs = tmp_tctx.instantiate_mvars(sl.get_rhs());
                    tout() << "(" << sl.get_id() << ") "
                    << "[" << new_lhs << " --> " << new_rhs << "]\n";);

    if (!instantiate_emetas(tmp_tctx, sl.get_num_emeta(), sl.get_emetas(), sl.get_instances()))
        return simp_result(e);

    for (unsigned i = 0; i < sl.get_num_umeta(); i++) {
        if (!tmp_tctx.is_uassigned(i)) return simp_result(e);
    }

    expr new_lhs = tmp_tctx.instantiate_mvars(sl.get_lhs());
    expr new_rhs = tmp_tctx.instantiate_mvars(sl.get_rhs());

    if (sl.is_perm()) {
        // TODO(dhs): restore light-lt
        if (!is_lt(new_rhs, new_lhs, false)) {
            lean_simp_trace(tmp_tctx, name({"simplifier", "perm"}),
                            tout() << "perm rejected: " << new_rhs << " !< " << new_lhs << "\n";);
            return simp_result(e);
        }
    }

    expr pf = tmp_tctx.instantiate_mvars(sl.get_proof());
    return simp_result(new_rhs, pf);
}

/* Congruence */

simp_result simplifier::congr_fun_arg(simp_result const & r_f, simp_result const & r_arg) {
    if (!r_f.has_proof() && !r_arg.has_proof()) return simp_result(mk_app(r_f.get_new(), r_arg.get_new()));
    else if (!r_f.has_proof()) return congr_arg(r_f.get_new(), r_arg);
    else if (!r_arg.has_proof()) return congr_fun(r_f, r_arg.get_new());
    else return congr(r_f, r_arg);
}

simp_result simplifier::congr(simp_result const & r_f, simp_result const & r_arg) {
    lean_assert(r_f.has_proof() && r_arg.has_proof());
    // theorem congr {A B : Type} {f₁ f₂ : A → B} {a₁ a₂ : A} (H₁ : f₁ = f₂) (H₂ : a₁ = a₂) : f₁ a₁ = f₂ a₂
    expr e  = mk_app(r_f.get_new(), r_arg.get_new());
    expr pf = mk_congr(m_tctx, r_f.get_proof(), r_arg.get_proof());
    return simp_result(e, pf);
}

simp_result simplifier::congr_fun(simp_result const & r_f, expr const & arg) {
    lean_assert(r_f.has_proof());
    // theorem congr_fun {A : Type} {B : A → Type} {f g : Π x, B x} (H : f = g) (a : A) : f a = g a
    expr e  = mk_app(r_f.get_new(), arg);
    expr pf = mk_congr_fun(m_tctx, r_f.get_proof(), arg);
    return simp_result(e, pf);
}

simp_result simplifier::congr_arg(expr const & f, simp_result const & r_arg) {
    lean_assert(r_arg.has_proof());
    // theorem congr_arg {A B : Type} {a₁ a₂ : A} (f : A → B) : a₁ = a₂ → f a₁ = f a₂
    expr e  = mk_app(f, r_arg.get_new());
    expr pf = mk_congr_arg(m_tctx, f, r_arg.get_proof());
    return simp_result(e, pf);
}

/* Note: handles reflexivity */
simp_result simplifier::congr_funs(simp_result const & r_f, buffer<expr> const & args) {
    // congr_fun : ∀ {A : Type} {B : A → Type} {f g : Π (x : A), B x}, f = g → (∀ (a : A), f a = g a)
    expr e = r_f.get_new();
    for (unsigned i = 0; i < args.size(); ++i) {
        e  = mk_app(e, args[i]);
    }
    if (!r_f.has_proof()) return simp_result(e);
    expr pf = r_f.get_proof();
    for (unsigned i = 0; i < args.size(); ++i) {
        pf = mk_app(m_tctx, get_congr_fun_name(), pf, args[i]);
    }
    return simp_result(e, pf);
}

simp_result simplifier::try_congrs(expr const & e) {
    simp_lemmas_for const * sls = m_slss.find(m_rel);
    if (!sls) return simp_result(e);

    list<user_congr_lemma> const * cls = sls->find_congr(e);
    if (!cls) return simp_result(e);

    simp_result r(e);
    for (user_congr_lemma const & cl : *cls) {
        if (r.has_proof()) break;
        r = try_congr(e, cl);
    }
    return r;
}

simp_result simplifier::try_congr(expr const & e, user_congr_lemma const & cl) {
    tmp_type_context tmp_tctx(m_tctx, cl.get_num_umeta(), cl.get_num_emeta());
    if (!tmp_tctx.is_def_eq(e, cl.get_lhs())) return simp_result(e);

    lean_simp_trace(tmp_tctx, name({"simplifier", "congruence"}),
                    expr new_lhs = tmp_tctx.instantiate_mvars(cl.get_lhs());
                    expr new_rhs = tmp_tctx.instantiate_mvars(cl.get_rhs());
                    tout() << "(" << cl.get_id() << ") "
                    << "[" << new_lhs << " =?= " << new_rhs << "]\n";);

    /* First, iterate over the congruence hypotheses */
    bool failed = false;
    bool simplified = false;
    list<expr> const & congr_hyps = cl.get_congr_hyps();
    for (expr const & m : congr_hyps) {
        type_context::tmp_locals local_factory(m_tctx);
        expr m_type = tmp_tctx.instantiate_mvars(tmp_tctx.infer(m));

        while (is_pi(m_type)) {
            expr d = instantiate_rev(binding_domain(m_type), local_factory.as_buffer().size(), local_factory.as_buffer().data());
            expr l = local_factory.push_local(binding_name(m_type), d, binding_info(m_type));
            lean_assert(!has_metavar(l));
            m_type = binding_body(m_type);
        }
        m_type = instantiate_rev(m_type, local_factory.as_buffer().size(), local_factory.as_buffer().data());

        expr h_rel, h_lhs, h_rhs;
        lean_verify(is_simp_relation(tmp_tctx.env(), m_type, h_rel, h_lhs, h_rhs) && is_constant(h_rel));
        {
            flet<name> set_name(m_rel, const_name(h_rel));
            flet<simp_lemmas> set_ctx_slss(m_ctx_slss, m_contextual ? add_to_slss(m_ctx_slss, local_factory.as_buffer()) : m_ctx_slss);

            h_lhs = tmp_tctx.instantiate_mvars(h_lhs);
            lean_assert(!has_metavar(h_lhs));

            simp_result r_congr_hyp;
            if (m_contextual) {
                freset<simplify_cache> reset_cache(m_cache);
                r_congr_hyp = simplify(h_lhs);
            } else {
                r_congr_hyp = simplify(h_lhs);
            }

            if (r_congr_hyp.has_proof())
                simplified = true;

            expr hyp = finalize(m_tctx, m_rel, r_congr_hyp).get_proof();
            if (!tmp_tctx.is_def_eq(m, local_factory.mk_lambda(hyp))) {
                    failed = true;
                    break;
            }
        }
    }

    if (failed || !simplified) return simp_result(e);

    if (!instantiate_emetas(tmp_tctx, cl.get_num_emeta(), cl.get_emetas(), cl.get_instances())) return simp_result(e);

    for (unsigned i = 0; i < cl.get_num_umeta(); i++) {
        if (!tmp_tctx.is_uassigned(i)) return simp_result(e);
    }

    expr e_s = tmp_tctx.instantiate_mvars(cl.get_rhs());
    expr pf = tmp_tctx.instantiate_mvars(cl.get_proof());
    return simp_result(e_s, pf);
}

bool simplifier::instantiate_emetas(tmp_type_context & tmp_tctx, unsigned num_emeta, list<expr> const & emetas, list<bool> const & instances) {
    bool failed = false;
    unsigned i = num_emeta;
    for_each2(emetas, instances, [&](expr const & m, bool const & is_instance) {
            i--;
            if (failed) return;
            expr m_type = tmp_tctx.instantiate_mvars(tmp_tctx.infer(m));
            lean_assert(!has_metavar(m_type));

            if (tmp_tctx.is_eassigned(i)) return;

            if (is_instance) {
                if (auto v = m_tctx.mk_class_instance(m_type)) {
                    if (!tmp_tctx.is_def_eq(m, *v)) {
                        lean_simp_trace(tmp_tctx, name({"simplifier", "failure"}),
                                        tout() << "unable to assign instance for: " << m_type << "\n";);
                        failed = true;
                        return;
                    }
                } else {
                    lean_simp_trace(tmp_tctx, name({"simplifier", "failure"}),
                                    tout() << "unable to synthesize instance for: " << m_type << "\n";);
                    failed = true;
                    return;
                }
            }

            if (tmp_tctx.is_eassigned(i)) return;

            // Note: m_type has no metavars
            if (m_tctx.is_prop(m_type)) {
                if (auto pf = prove(m_type)) {
                    lean_verify(tmp_tctx.is_def_eq(m, *pf));
                    return;
                }
            }

            lean_simp_trace(tmp_tctx, name({"simplifier", "failure"}),
                            tout() << "failed to assign: " << m << " : " << m_type << "\n";);

            failed = true;
            return;
        });

    return !failed;
}

template<typename F>
optional<simp_result> simplifier::synth_congr(expr const & e, F && simp) {
    static_assert(std::is_same<typename std::result_of<F(expr const & e)>::type, simp_result>::value,
                  "synth_congr: simp must take expressions to simp_results");
    lean_assert(is_app(e));
    buffer<expr> args;
    expr f = get_app_args(e, args);
    auto congr_lemma = mk_specialized_congr_simp(m_tctx, e);
    if (!congr_lemma) return optional<simp_result>();
    expr proof = congr_lemma->get_proof();
    expr type = congr_lemma->get_type();
    unsigned i = 0;
    bool has_proof              = false;
    /* bool has_cast            = false; */
    buffer<expr> subst;
    for (congr_arg_kind const & ckind : congr_lemma->get_arg_kinds()) {
        switch (ckind) {
        case congr_arg_kind::HEq:
            lean_unreachable();
        case congr_arg_kind::Fixed:
            proof = mk_app(proof, args[i]);
            subst.push_back(args[i]);
            type = binding_body(type);
            break;
        case congr_arg_kind::FixedNoParam:
            break;
        case congr_arg_kind::Eq:
            proof = mk_app(proof, args[i]);
            subst.push_back(args[i]);
            type = binding_body(type);
            {
                simp_result r_arg = simp(args[i]);
                if (r_arg.has_proof())
                    has_proof = true;
                r_arg = finalize(m_tctx, m_rel, r_arg);
                proof = mk_app(proof, r_arg.get_new(), r_arg.get_proof());
                subst.push_back(r_arg.get_new());
                subst.push_back(r_arg.get_proof());
                type = binding_body(binding_body(type));
            }
            break;
        case congr_arg_kind::Cast:
            proof = mk_app(proof, args[i]);
            subst.push_back(args[i]);
            type = binding_body(type);
            /* has_cast = true; */
            break;
        }
        i++;
    }
    lean_assert(is_eq(type));
    expr rhs   = instantiate_rev(app_arg(type), subst.size(), subst.data());
    expr e_new = remove_unnecessary_casts(rhs);
    simp_result r;
    if (has_proof) r = simp_result(e_new, proof);
    else r = simp_result(e_new);

    /* TODO(dhs): re-integrate
    if (has_cast) {
        if (auto r_norm = normalize_subsingleton_args(e_new))
            r = join(r, *r_norm);
    }
    */
    return optional<simp_result>(r);
}

expr simplifier::remove_unnecessary_casts(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    ss_param_infos ss_infos = get_specialized_subsingleton_info(m_tctx, e);
    int i = -1;
    for (ss_param_info const & ss_info : ss_infos) {
        i++;
        if (ss_info.is_subsingleton()) {
            while (is_constant(get_app_fn(args[i]))) {
                buffer<expr> cast_args;
                expr f_cast = get_app_args(args[i], cast_args);
                name n_f = const_name(f_cast);
                if (n_f == get_eq_rec_name() || n_f == get_eq_drec_name() || n_f == get_eq_nrec_name()) {
                    lean_assert(cast_args.size() == 6);
                    expr major_premise = cast_args[5];
                    expr f_major_premise = get_app_fn(major_premise);
                    if (is_constant(f_major_premise) && const_name(f_major_premise) == get_eq_refl_name())
                        args[i] = cast_args[3];
                    else
                        break;
                } else {
                    break;
                }
            }
        }
    }
    return mk_app(f, args);
}

vm_obj tactic_simplify_core(vm_obj const & prove_fn, vm_obj const & rel, vm_obj const & lemmas, vm_obj const & e, vm_obj const & s0) {
    tactic_state const & s   = to_tactic_state(s0);
    try {
        type_context tctx    = mk_type_context_for(s, transparency_mode::Reducible);
        simp_result result   = simplify(tctx, to_name(rel), to_simp_lemmas(lemmas), prove_fn, to_expr(e));

        if (result.has_proof()) {
            return mk_tactic_success(mk_vm_pair(to_obj(result.get_new()), to_obj(result.get_proof())), s);
        } else {
            return mk_tactic_exception("simp tactic failed to simplify", s);
        }
    } catch (exception & e) {
        return mk_tactic_exception(e, s);
    }
}

/* Setup and teardown */
void initialize_simplifier() {
    register_trace_class(name({"simplifier", "congruence"}));
    register_trace_class(name({"simplifier", "user_extensions"}));
    register_trace_class(name({"simplifier", "failure"}));
    register_trace_class(name({"simplifier", "perm"}));
    register_trace_class(name({"simplifier", "canonize"}));
    register_trace_class(name({"simplifier", "prove"}));
    register_trace_class(name({"simplifier", "rewrite"}));
    register_trace_class(name({"simplifier", "rewrite", "assoc"}));
    register_trace_class(name({"simplifier", "rewrite", "ac"}));
    register_trace_class(name({"simplifier", "theory"}));
    register_trace_class(name({"debug", "simplifier", "try_rewrite"}));
    register_trace_class(name({"debug", "simplifier", "try_rewrite", "assoc"}));

    g_simplify_max_steps           = new name{"simplify", "max_steps"};
    g_simplify_max_rewrites        = new name{"simplify", "max_rewrites"};
    g_simplify_rewrite_ac          = new name{"simplify", "rewrite_ac"};
    g_simplify_memoize             = new name{"simplify", "memoize"};
    g_simplify_contextual          = new name{"simplify", "contextual"};
    g_simplify_lift_eq             = new name{"simplify", "lift_eq"};
    g_simplify_canonize_proofs     = new name{"simplify", "canonize_proofs"};

    register_unsigned_option(*g_simplify_max_steps, LEAN_DEFAULT_SIMPLIFY_MAX_STEPS,
                             "(simplify) max number of (large) steps in simplification");
    register_unsigned_option(*g_simplify_max_rewrites, LEAN_DEFAULT_SIMPLIFY_MAX_REWRITES,
                             "(simplify) max number of rewrites in simplification");
    register_bool_option(*g_simplify_rewrite_ac, LEAN_DEFAULT_SIMPLIFY_REWRITE_AC,
                         "(simplify) rewrite mod AC for AC operators");
    register_bool_option(*g_simplify_memoize, LEAN_DEFAULT_SIMPLIFY_MEMOIZE,
                         "(simplify) memoize simplifications");
    register_bool_option(*g_simplify_contextual, LEAN_DEFAULT_SIMPLIFY_CONTEXTUAL,
                         "(simplify) use contextual simplification");
    register_bool_option(*g_simplify_lift_eq, LEAN_DEFAULT_SIMPLIFY_LIFT_EQ,
                         "(simplify) try simplifying with equality when no progress over other relation");
    register_bool_option(*g_simplify_canonize_proofs, LEAN_DEFAULT_SIMPLIFY_CANONIZE_PROOFS,
                         "(simplify) canonize_proofs");

    DECLARE_VM_BUILTIN(name({"tactic", "simplify_core"}), tactic_simplify_core);
}

void finalize_simplifier() {
    delete g_simplify_canonize_proofs;
    delete g_simplify_lift_eq;
    delete g_simplify_contextual;
    delete g_simplify_memoize;
    delete g_simplify_rewrite_ac;
    delete g_simplify_max_rewrites;
    delete g_simplify_max_steps;
}

/* Entry point */
simp_result simplify(type_context & ctx, name const & rel, simp_lemmas const & simp_lemmas, vm_obj const & prove_fn, expr const & e) {
    return simplifier(ctx, rel, simp_lemmas, prove_fn)(e);
}

}
