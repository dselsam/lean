/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "kernel/inductive/inductive.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "util/sexpr/option_declarations.h"
#include "library/locals.h"
#include "library/app_builder.h"
#include "library/constants.h"
#include "library/module.h"
#include "library/trace.h"
#include "library/type_context.h"
#include "library/attribute_manager.h"
#include "library/inductive_compiler/ginductive.h"
#include "library/inductive_compiler/compiler.h"
#include "library/inductive_compiler/basic.h"
#include "library/inductive_compiler/mutual.h"

namespace lean {

static name * g_mutual_prefix = nullptr;

// TODO(dhs): move to util
static expr get_ind_result_type(type_context & tctx, expr const & ind) {
    expr ind_type = tctx.relaxed_whnf(mlocal_type(ind));
    type_context::tmp_locals locals(tctx);
    while (is_pi(ind_type)) {
        ind_type = instantiate(binding_body(ind_type), locals.push_local_from_binding(ind_type));
        ind_type = tctx.relaxed_whnf(ind_type);
    }
    lean_assert(is_sort(ind_type));
    return ind_type;
}

class compile_mutual_to_basic_fn {
    environment const     & m_env;
    ginductive_decl const & m_mut_decl;
    aux_type_context        m_aux_tctx;
    type_context &          m_tctx;

    buffer<expr>            m_index_types;
    expr                    m_full_index_type;
    buffer<expr>            m_makers;
    buffer<expr>            m_putters;

    buffer<expr>            m_new_inds;
    buffer<buffer<expr> >   m_new_intro_rules;

    expr to_sigma_type(expr const & _ty) {
        expr ty = m_tctx.relaxed_whnf(_ty);
        if (!is_pi(ty)) {
            return mk_constant(get_unit_name());
        } else {
            type_context::tmp_locals locals(m_tctx);
            expr l    = locals.push_local_from_binding(ty);
            expr dom  = binding_domain(ty);
            expr rest = locals.mk_lambda(to_sigma_type(instantiate(binding_body(ty), l)));
            return mk_app(m_tctx, get_sigma_name(), {dom, rest});
        }
    }

    expr mk_sum(unsigned num_args, expr const * args) {
        expr sum = args[num_args-1];
        for (unsigned i = num_args - 2; i + 1 > 0; --i) {
            sum = mk_app(m_tctx, get_sum_name(), args[i], sum);
        }
        return sum;
    }

    void compute_index_types() {
        for (expr const & ind : m_mut_decl.get_inds()) {
            m_index_types.push_back(to_sigma_type(mlocal_type(ind)));
            lean_trace(name({"inductive_compiler", "mutual", "index_types"}), tout() << mlocal_name(ind) << " ==> " << m_index_types.back() << "\n";);
        }
        m_full_index_type = mk_sum(m_index_types.size(), m_index_types.data());
        lean_trace(name({"inductive_compiler", "mutual", "full_index_type"}), tout() << m_full_index_type << "\n";);
    }

    expr to_maker(expr const & _ty) {
        type_context::tmp_locals locals(m_tctx);
        expr ty = m_tctx.relaxed_whnf(_ty);
        // TODO(dhs): do I need to whnf inside? If so I need to re-structure this loop.
        while (is_pi(ty)) {
            expr l = locals.push_local(binding_name(ty), binding_domain(ty), binding_info(ty));
            ty = m_tctx.relaxed_whnf(instantiate(binding_body(ty), l));
        }
        expr maker = mk_constant(get_unit_star_name());
        expr stype = mk_constant(get_unit_name());
        buffer<expr> ls = locals.as_buffer();
        for (unsigned i = ls.size() - 1; i + 1 > 0; --i) {
            expr const & l = ls[i];
            expr A = m_tctx.infer(l);
            level l1 = get_level(m_tctx, A);
            level l2 = get_level(m_tctx, stype);
            stype = m_tctx.mk_lambda(l, stype);
            maker = mk_app(mk_constant(get_sigma_mk_name(), {l1, l2}), A, stype, l, maker);
            stype = mk_app(m_tctx, get_sigma_name(), {A, stype});
        }
        return locals.mk_lambda(maker);
    }

    void compute_makers() {
        for (expr const & ind : m_mut_decl.get_inds()) {
            m_makers.push_back(to_maker(mlocal_type(ind)));
            lean_trace(name({"inductive_compiler", "mutual", "makers"}), tout() << mlocal_name(ind) << " ==> " << m_makers.back() << "\n";);
        }
    }

    expr to_putter(unsigned ind_idx) {
        type_context::tmp_locals locals(m_tctx);
        unsigned num_inds = m_index_types.size();
        expr l = locals.push_local(name("idx"), m_index_types[ind_idx]);

        expr putter;
        if (ind_idx == num_inds - 1) {
            putter = mk_app(m_tctx, get_sum_inr_name(), m_index_types[ind_idx - 1], m_index_types[ind_idx], l);
            ind_idx--;
        } else {
            putter = mk_app(m_tctx, get_sum_inl_name(), m_index_types[ind_idx], mk_sum(num_inds - ind_idx - 1, m_index_types.data() + ind_idx + 1), l);
        }
        for (unsigned i = ind_idx; i > 0; --i) {
            putter = mk_app(m_tctx, get_sum_inr_name(), m_index_types[i - 1], mk_sum(num_inds - i, m_index_types.data() + i), putter);
        }
        return locals.mk_lambda(putter);
    }

    void compute_putters() {
        for (unsigned i = 0; i < m_mut_decl.get_inds().size(); ++i) {
            m_putters.push_back(to_putter(i));
            lean_trace(name({"inductive_compiler", "mutual", "putters"}), tout() << mlocal_name(m_mut_decl.get_inds()[i]) << " ==> " << m_putters.back() << "\n";);
        }
    }

    name mk_single_name() {
        name n = *g_mutual_prefix;
        for (unsigned i = 0; i < m_mut_decl.get_inds().size(); ++i) {
            n = n + mlocal_name(m_mut_decl.get_inds()[i]);
        }
        return n;
    }

    void compute_new_ind() {
        expr ind = mk_local(mk_single_name(), mk_arrow(m_full_index_type, get_ind_result_type(m_tctx, m_mut_decl.get_inds()[0])));
        lean_trace(name({"inductive_compiler", "mutual", "new_ind"}), tout() << mlocal_name(ind) << " : " << mlocal_type(ind) << "\n";);
        m_new_inds.push_back(ind);
    }

    optional<expr> translate_ind_app(expr const & app) {
        buffer<expr> args;
        expr fn = get_app_args(app, args);
        for (unsigned i = 0; i < m_mut_decl.get_inds().size(); ++i) {
            expr ind = m_mut_decl.get_inds()[i];
            if (fn == ind)
                return some_expr(mk_app(m_new_inds[0], mk_app(m_putters[i], mk_app(m_makers[i], args))));
        }
        return none_expr();
    }

    optional<expr> translate_ir_arg(expr const & arg_type) {
        type_context::tmp_locals locals(m_tctx);
        expr ty = m_tctx.relaxed_whnf(arg_type);
        while (is_pi(ty)) {
            ty = instantiate(binding_body(ty), locals.push_local_from_binding(ty));
            ty = m_tctx.relaxed_whnf(ty);
        }
        if (auto e = translate_ind_app(ty))
            return some_expr(locals.mk_pi(*e));
        else
            return none_expr();
    }

    expr translate_ir(expr const & ir) {
        name ir_name = mk_single_name() + mlocal_name(ir);
        type_context::tmp_locals locals(m_tctx);
        expr ty = m_tctx.relaxed_whnf(mlocal_type(ir));
        while (is_pi(ty)) {
            expr arg_type = binding_domain(ty);
            expr l;
            if (auto new_arg_type = translate_ir_arg(arg_type)) {
                l = locals.push_local(binding_name(ty), *new_arg_type);
            } else {
                l = locals.push_local(binding_name(ty), arg_type);
            }
            ty = instantiate(binding_body(ty), l);
            ty = m_tctx.relaxed_whnf(ty);
        }
        expr result_type;
        if (auto new_result_type = translate_ind_app(ty))
            result_type = *new_result_type;
        else
            result_type = ty;

        return mk_local(ir_name, locals.mk_pi(result_type));
    }

    void compute_new_intro_rules() {
        m_new_intro_rules.emplace_back();
        for (unsigned i = 0; i < m_mut_decl.get_inds().size(); ++i) {
            buffer<expr> const & irs = m_mut_decl.get_intro_rules()[i];
            for (expr const & ir : irs) {
                m_new_intro_rules.back().push_back(translate_ir(ir));
                lean_trace(name({"inductive_compiler", "mutual", "new_irs"}), tout()
                           << mlocal_name(ir) << " : " << mlocal_type(ir) << "\n==>\n"
                           << mlocal_name(m_new_intro_rules.back().back()) << " : " << mlocal_type(m_new_intro_rules.back().back()) << "\n";);
            }
        }
    }

public:
    compile_mutual_to_basic_fn(environment const & env, ginductive_decl const & mut_decl):
        m_env(env), m_mut_decl(mut_decl), m_aux_tctx(env), m_tctx(m_aux_tctx.get()) {}

    pair<ginductive_decl, mutual_decl_aux> operator()() {
        compute_index_types();
        compute_makers();
        compute_putters();
        compute_new_ind();
        compute_new_intro_rules();

        return mk_pair(ginductive_decl(m_mut_decl.get_lp_names(), m_mut_decl.get_params(),
                                       m_new_inds, m_new_intro_rules),
                       mutual_decl_aux(m_index_types, m_full_index_type, m_makers, m_putters));
    }
};

pair<ginductive_decl, mutual_decl_aux> compile_mutual_to_basic(environment const & env, ginductive_decl const & mut_decl) {
    return compile_mutual_to_basic_fn(env, mut_decl)();
}

// TODO(dhs): need to take the basic ginductive_decl as well (if only for names)
class postprocess_mutual_fn {
    environment             m_env;
    ginductive_decl const & m_mut_decl;
    ginductive_decl const & m_basic_decl;
    mutual_decl_aux const & m_mut_aux;

    aux_type_context        m_aux_tctx;
    type_context &          m_tctx;

    buffer<expr>            m_c_inds;

public:
    postprocess_mutual_fn(environment const & env, ginductive_decl const & mut_decl, ginductive_decl const & basic_decl, mutual_decl_aux const & mut_aux):
        m_env(env), m_mut_decl(mut_decl), m_basic_decl(basic_decl), m_mut_aux(mut_aux), m_aux_tctx(env), m_tctx(m_aux_tctx.get()) {}

    void define_ind_types() {
        for (unsigned ind_idx = 0; ind_idx < m_mut_decl.get_inds().size(); ++ind_idx) {
            expr const & ind = m_mut_decl.get_inds()[ind_idx];
            type_context::tmp_locals locals(m_tctx);
            expr ty = m_tctx.relaxed_whnf(mlocal_type(ind));
            while (is_pi(ty)) {
                expr l = locals.push_local(binding_name(ty), binding_domain(ty), binding_info(ty));
                ty = m_tctx.relaxed_whnf(instantiate(binding_body(ty), l));
            }
            buffer<expr> args(m_mut_decl.get_params());
            args.push_back(mk_app(m_mut_aux.get_putters()[ind_idx],
                                  mk_app(m_mut_aux.get_makers()[ind_idx], locals.as_buffer())));
            expr new_ind_val = locals.mk_lambda(mk_app(mk_constant(mlocal_name(m_basic_decl.get_inds()[0]), param_names_to_levels(to_list(m_mut_decl.get_lp_names()))),
                                                       args));
            expr new_ind_type = mlocal_type(ind);
            new_ind_val = Fun(m_mut_decl.get_params(), new_ind_val);
            new_ind_type = Pi(m_mut_decl.get_params(), new_ind_type);

            lean_trace(name({"inductive_compiler", "mutual", "new_inds"}), tout()
                       << mlocal_name(ind) << " : " << new_ind_type << " :=\n  " << new_ind_val << "\n";);
            // TODO(dhs): set attributes? irreducible? constructor-like? no-pattern?
            m_env = module::add(m_env, check(m_env, mk_definition(m_env, mlocal_name(ind), to_list(m_mut_decl.get_lp_names()), new_ind_type, new_ind_val)));
        }
    }

    void compute_c_inds() {
        for (expr const & ind : m_mut_decl.get_inds()) {
            m_c_inds.push_back(mk_app(mk_constant(mlocal_name(ind), param_names_to_levels(to_list(m_mut_decl.get_lp_names()))),
                                      m_mut_decl.get_params()));
        }
    }

    void define_intro_rules() {
        compute_c_inds();
        // definition foo.mk (A : Type) := @FBR.fmk A
        unsigned basic_ir_idx = 0;
        for (unsigned ind_idx = 0; ind_idx < m_mut_decl.get_inds().size(); ++ind_idx) {
            buffer<expr> const & irs = m_mut_decl.get_intro_rules()[ind_idx];
            for (expr const & ir : irs) {
                expr new_ir_val = Fun(m_mut_decl.get_params(), mk_app(mk_constant(mlocal_name(m_basic_decl.get_intro_rules()[0][basic_ir_idx]),
                                                                                  param_names_to_levels(to_list(m_mut_decl.get_lp_names()))),
                                                                      m_mut_decl.get_params()));
                expr new_ir_type = Pi(m_mut_decl.get_params(), replace_locals(mlocal_type(ir), m_mut_decl.get_inds(), m_c_inds));
                lean_trace(name({"inductive_compiler", "mutual", "new_irs"}), tout()
                           << mlocal_name(ir) << " : " << new_ir_type << " :=\n  " << new_ir_val << "\n";);
                m_env = module::add(m_env, check(m_env, mk_definition(m_env, mlocal_name(ir), to_list(m_mut_decl.get_lp_names()), new_ir_type, new_ir_val)));
                basic_ir_idx++;
            }
        }
    }

    environment operator()() {
        define_ind_types();
        define_intro_rules();
//        define_cases_on();
        return m_env;
    }
};
/*
environment define_ind_types(environment const & env, ginductive_decl const & mut_decl,

        type_context::tmp_locals locals(m_tctx);
        expr ty = m_tctx.relaxed_whnf(_ty);
          while (is_pi(ty)) {
            expr l = locals.push_local(binding_name(ty), binding_domain(ty), binding_info(ty));
            ty = m_tctx.relaxed_whnf(instantiate(binding_body(ty), l));
        }
        expr maker = mk_constant(get_unit_star_name());
        expr stype = mk_constant(get_unit_name());
        buffer<expr> ls = locals.as_buffer();
        for (unsigned i = ls.size() - 1; i + 1 > 0; --i) {
            expr const & l = ls[i];
            expr A = m_tctx.infer(l);
            level l1 = get_level(m_tctx, A);
            level l2 = get_level(m_tctx, stype);
            stype = m_tctx.mk_lambda(l, stype);
            maker = mk_app(mk_constant(get_sigma_mk_name(), {l1, l2}), A, stype, l, maker);
            stype = mk_app(m_tctx, get_sigma_name(), {A, stype});
        }
        return locals.mk_lambda(maker);
*/
environment post_process_mutual(environment const & env, options const & opts, name_map<implicit_infer_kind> const & implicit_infer_map,
                                ginductive_decl const & mut_decl, ginductive_decl const & basic_decl, mutual_decl_aux const & mut_aux) {
    return postprocess_mutual_fn(env, mut_decl, basic_decl, mut_aux)();
}

void initialize_inductive_compiler_mutual() {
    register_trace_class(name({"inductive_compiler", "mutual"}));
    register_trace_class(name({"inductive_compiler", "mutual", "index_types"}));
    register_trace_class(name({"inductive_compiler", "mutual", "full_index_type"}));
    register_trace_class(name({"inductive_compiler", "mutual", "makers"}));
    register_trace_class(name({"inductive_compiler", "mutual", "putters"}));
    register_trace_class(name({"inductive_compiler", "mutual", "new_ind"}));
    register_trace_class(name({"inductive_compiler", "mutual", "new_irs"}));
    register_trace_class(name({"inductive_compiler", "mutual", "new_inds"}));

    g_mutual_prefix = new name(name::mk_internal_unique_name());
}

void finalize_inductive_compiler_mutual() {
    delete g_mutual_prefix;
}
}
