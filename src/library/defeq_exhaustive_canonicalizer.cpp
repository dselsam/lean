/*
Copyright (c) 2016 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "util/interrupt.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/expr_maps.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/inductive/inductive.h"
#include "library/trace.h"
#include "library/util.h"
#include "library/fun_info.h"
#include "library/defeq_canonicalizer.h"

namespace lean {

class defeq_canonicalize_exhaustively_fn {
    type_context           & m_ctx;
    bool                     m_need_restart{false};

    bool                     m_memoize;
    bool                     m_canonicalize_proofs;

    /* Cache */
    expr_struct_map<expr>    m_cache;

    optional<expr> cache_lookup(expr const & e) {
        auto it = m_cache.find(e);
        if (it == m_cache.end()) return none_expr();
        else return some_expr(it->second);
    }

    void cache_save(expr const & e, expr const & e_simp) {
        m_cache.insert(mk_pair(e, e_simp));
    }

    environment const & env() const { return m_ctx.env(); }

    /* Simplification */
    expr defeq_canonicalize_exhaustively(expr const & _e) {
        expr e = _e;
        lean_trace_inc_depth("defeq_exhaustive_canonicalizer");
        lean_trace_d("defeq_exhaustive_canonicalizer", tout() << e << "\n";);

        while (true) {
            expr e_start = e;
            check_system("defeq_exhaustive_canonicalizer");

            if (m_memoize) {
                if (auto it = cache_lookup(e)) return *it;
            }

            switch (e.kind()) {
            case expr_kind::Local:
            case expr_kind::Meta:
            case expr_kind::Sort:
            case expr_kind::Constant:
                break;
            case expr_kind::Var:
                lean_unreachable();
            case expr_kind::Macro:
                e = defeq_canonicalize_exhaustively_macro(e);
                break;
            case expr_kind::Lambda:
            case expr_kind::Pi:
                e = defeq_canonicalize_exhaustively_binding(e);
                break;
            case expr_kind::App:
                e = defeq_canonicalize_exhaustively_app(e);
                break;
            case expr_kind::Let:
                lean_unreachable();
                // whnf expands let-expressions
            }
            if (e == e_start) break;
        }
        if (m_memoize) cache_save(_e, e);
        return e;
    }

    expr defeq_canonicalize_exhaustively_macro(expr const & e) {
        buffer<expr> new_args;
        for (unsigned i = 0; i < macro_num_args(e); i++)
            new_args.push_back(defeq_canonicalize_exhaustively(macro_arg(e, i)));
        return update_macro(e, new_args.size(), new_args.data());
    }

    expr defeq_canonicalize_exhaustively_binding(expr const & e) {
        expr d = defeq_canonicalize_exhaustively(binding_domain(e));
        expr l = m_ctx.push_local(binding_name(e), d, binding_info(e));
        expr b = defeq_canonicalize_exhaustively(instantiate(binding_body(e), l));
        b = m_ctx.abstract_locals(b, 1, &l);
        m_ctx.pop_local();
        return update_binding(e, d, b);
    }

    expr defeq_canonicalize_exhaustively_app(expr const & e) {
        buffer<expr> args;
        bool modified = false;
        expr f        = get_app_args(e, args);
        fun_info info = get_fun_info(m_ctx, f, args.size());
        unsigned i    = 0;
        for (param_info const & pinfo : info.get_params_info()) {
            lean_assert(i < args.size());
            expr new_a;
            if (pinfo.is_inst_implicit() || (m_canonicalize_proofs && pinfo.is_prop())) {
                new_a = ::lean::defeq_canonicalize(m_ctx, args[i], m_need_restart);
                lean_trace(name({"defeq_exhaustive_canonicalizer", "canonicalize"}),
                           tout() << "\n" << args[i] << "\n===>\n" << new_a << "\n";);
            } else if (pinfo.is_prop() || pinfo.is_subsingleton()) {
                /* Ignore propositions and subsingletons */
                new_a = args[i];
            } else {
                new_a = defeq_canonicalize_exhaustively(args[i]);
            }
            if (new_a != args[i])
                modified = true;
            args[i] = new_a;
            i++;
        }
        for (; i < args.size(); i++) {
            expr new_a = defeq_canonicalize_exhaustively(args[i]);
            if (new_a != args[i])
                modified = true;
            args[i] = new_a;
        }

        if (!modified)
            return e;
        else
            return mk_app(f, args);
    }

public:
    defeq_canonicalize_exhaustively_fn(type_context & ctx, bool memoize, bool canonicalize_proofs):
        m_ctx(ctx),
        m_memoize(memoize),
        m_canonicalize_proofs(canonicalize_proofs)
        { }

    ~defeq_canonicalize_exhaustively_fn() {}

    expr operator()(expr e) {
        scope_trace_env scope(env(), m_ctx);
        while (true) {
            m_need_restart = false;
            e = defeq_canonicalize_exhaustively(e);
            if (!m_need_restart)
                return e;
            m_cache.clear();
        }
    }
};

/* Entry point */
expr defeq_canonicalize_exhaustively(type_context & ctx, expr const & e, bool memoize, bool canonicalize_proofs) {
    return defeq_canonicalize_exhaustively_fn(ctx, memoize, canonicalize_proofs)(e);
}

/* Setup and teardown */
void initialize_defeq_exhaustive_canonicalizer() {
    register_trace_class("defeq_exhaustive_canonicalizer");
    register_trace_class(name({"defeq_exhaustive_canonicalizer", "canonicalize"}));
}

void finalize_defeq_exhaustive_canonicalizer() {
}
}
