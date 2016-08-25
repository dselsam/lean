/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "kernel/inductive/inductive.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "kernel/find_fn.h"
#include "kernel/replace_fn.h"
#include "util/sexpr/option_declarations.h"
#include "util/list_fn.h"
#include "util/fresh_name.h"
#include "library/locals.h"
#include "library/app_builder.h"
#include "library/constants.h"
#include "library/module.h"
#include "library/trace.h"
#include "library/type_context.h"
#include "library/attribute_manager.h"
#include "library/inductive_compiler/compiler.h"
#include "library/inductive_compiler/basic.h"
#include "library/inductive_compiler/nested.h"
#include "library/inductive_compiler/util.h"

namespace lean {

static name * g_nested_prefix = nullptr;

class add_nested_inductive_decl_fn {
    environment                   m_env;
    options const &               m_opts;
    name_map<implicit_infer_kind> m_implicit_infer_map;
    ginductive_decl const &       m_nested_decl;
    ginductive_decl               m_inner_decl;
    name                          m_prefix;

    type_context                  m_tctx;

    expr                          m_nested_occ;
    expr                          m_replacement; // needs to be applied to the locals in the nested_occ
    buffer<expr>                  m_locals_in_nested_occ;

    buffer<expr>                  m_ind_ir_locals;
    buffer<expr>                  m_ind_ir_cs;

    expr                          m_translator; // Pi (indices), nested_occ -> (next-layer)

    bool is_ind(expr const & e) {
        return is_local(e)
            && std::any_of(m_nested_decl.get_inds().begin(), m_nested_decl.get_inds().end(), [&](expr const & ind) { return e == ind; });
    }

    bool has_ind_occ(expr const & t) {
        return (bool)find(t, [&](expr const & e, unsigned) { return is_ind(e); });
    }

    bool is_param(expr const & e) {
        return is_local(e)
            && std::any_of(m_nested_decl.get_params().begin(), m_nested_decl.get_params().end(), [&](expr const & param) { return e == param; });
    }

    void collect_non_param_locals(expr const & e, collected_locals & collected_ls) {
        if (!has_local(e)) return;
        for_each(e, [&](expr const & e, unsigned) {
                if (!has_local(e)) return false;
                if (is_local(e) && !is_param(e) && !is_ind(e)) collected_ls.insert(e);
                return true;
            });
    }

    name mk_prefix() {
        return m_prefix;
    }

    void compute_mimic_ind() {
        buffer<expr> args;
        expr fn = get_app_args(m_nested_occ, args);
        name mimic_ind_name = mk_prefix() + const_name(fn);

        unsigned num_params = get_ginductive_num_params(m_env, const_name(fn));
        expr old_ind_partial_app = mk_app(fn, num_params, args.data());
        expr old_ind_type = m_tctx.infer(old_ind_partial_app);

        expr mimic_ind_type = Pi(m_locals_in_nested_occ, old_ind_type);
        expr mimic_ind = mk_local(mimic_ind_name, mimic_ind_type);
        lean_trace(name({"inductive_compiler", "nested", "mimic_ind"}),
                   tout() << mlocal_name(mimic_ind) << " : " << mlocal_type(mimic_ind) << "\n";);
        m_replacement = mimic_ind;

        m_inner_decl.get_inds().push_back(mimic_ind);
        buffer<expr> mimic_intro_rule_types;
        optional<list<name> > old_intro_rules = get_ginductive_intro_rules(m_env, const_name(fn));
        lean_assert(old_intro_rules);
        m_inner_decl.get_intro_rules().emplace_back();
        for (name const & old_ir_name : *old_intro_rules) {
            expr old_ir_type = m_tctx.infer(mk_app(mk_constant(old_ir_name, const_levels(fn)), num_params, args.data()));
            old_ir_type = replace(old_ir_type, [&](expr const & e, unsigned) {
                    if (e == old_ind_partial_app)
                        return some_expr(mk_app(m_replacement, m_locals_in_nested_occ));
                    else
                        return none_expr();
                });
            name mimic_ir_name = mk_prefix() + old_ir_name;
            expr mimic_ir_type = Pi(m_locals_in_nested_occ, old_ir_type);
            lean_trace(name({"inductive_compiler", "nested", "mimic_ir"}), tout() << mimic_ir_name << " : " << mimic_ir_type << "\n";);
            m_inner_decl.get_intro_rules().back().push_back(mk_local(mimic_ir_name, mimic_ir_type));
        }
    }

    expr mk_local_for(expr const & b) { return mk_local(mk_fresh_name(), binding_name(b), binding_domain(b), binding_info(b)); }
    expr mk_local_pp(name const & n, expr const & ty) { return mk_local(mk_fresh_name(), n, ty, binder_info()); }

    bool find_nested_occ_in_ir_arg_type_core(expr const & ty, optional<expr> outer_app) {
        buffer<expr> args;
        expr fn = get_app_args(ty, args);

        if (outer_app && is_ind(fn)) {
            // we found a nested occurrence
            collected_locals collected_ls;
            collect_non_param_locals(*outer_app, collected_ls);
            m_nested_occ = *outer_app;
            m_locals_in_nested_occ.append(collected_ls.get_collected());
            lean_trace(name({"inductive_compiler", "nested", "found_occ"}), tout()
                       << "(" << m_locals_in_nested_occ.size() << ") " << m_nested_occ << "\n";);
            compute_mimic_ind();
            return true;
        }

        if (is_constant(fn) && is_ginductive(m_env, const_name(fn))) {
            unsigned num_params = get_ginductive_num_params(m_env, const_name(fn));
            for (unsigned i = 0; i < num_params; ++i) {
                if (find_nested_occ_in_ir_arg_type_core(m_tctx.whnf(args[i]), some_expr(mk_app(fn, num_params, args.data()))))
                    return true;
            }
            for (unsigned i = num_params; i < args.size(); ++i) {
                if (has_ind_occ(args[i]))
                    throw exception("inductive type being declared cannot occur as an index argument of another inductive type");
            }
        }
        return false;
    }

    bool find_nested_occ_in_ir_arg_type(expr const & arg_ty) {
        expr ty = m_tctx.relaxed_whnf(arg_ty);
        if (!has_ind_occ(ty))
            return false;

        buffer<expr> inner_args;

        while (is_pi(ty)) {
            expr l = mk_local_for(ty);
            ty = instantiate(binding_body(ty), l);
            ty = m_tctx.relaxed_whnf(ty);
        }

        if (find_nested_occ_in_ir_arg_type_core(ty, none_expr()))
            return true;
        else
            return false;
    }

    bool find_nested_occ_in_ir_type(expr const & ir_type) {
        expr ty = m_tctx.relaxed_whnf(ir_type);
        while (is_pi(ty)) {
            expr arg_type = binding_domain(ty);
            if (find_nested_occ_in_ir_arg_type(arg_type))
                return true;
            expr l = mk_local_for(ty);
            ty = instantiate(binding_body(ty), l);
            ty = m_tctx.relaxed_whnf(ty);
        }
        return false;
    }

    bool find_nested_occ() {
        for (buffer<expr> const & irs : m_nested_decl.get_intro_rules()) {
            for (expr const & ir : irs) {
                if (find_nested_occ_in_ir_type(mlocal_type(ir)))
                    return true;
            }
        }
        return false;
    }

    bool matches_nested_occ_upto_locals(expr const & e, buffer<expr> const & locals) {
        return replace_locals(e, locals, m_locals_in_nested_occ) == m_nested_occ;
    }

    expr replace_nested_occs(expr const & e) {
        switch (e.kind()) {
        case expr_kind::Local:
        case expr_kind::Meta:
        case expr_kind::Sort:
        case expr_kind::Constant:
        case expr_kind::Lambda:
            return e;
        case expr_kind::Var:
            lean_unreachable();
        case expr_kind::Macro:
        {
            buffer<expr> new_args;
            unsigned nargs = macro_num_args(e);
            for (unsigned i = 0; i < nargs; i++)
                new_args.push_back(replace_nested_occs(macro_arg(e, i)));
            return update_macro(e, new_args.size(), new_args.data());
        }
        case expr_kind::Pi:
        {
            expr new_dom = replace_nested_occs(binding_domain(e));
            expr l = mk_local_for(e);
            expr new_body = binding_body(Pi(l, replace_nested_occs(instantiate(binding_body(e), l))));
            return update_binding(e, new_dom, new_body);
        }
        case expr_kind::App:
        {
            buffer<expr> args;
            expr fn = get_app_args(e, args);
            if (is_constant(fn) && is_ginductive(m_env, const_name(fn))) {
                unsigned num_params = get_ginductive_num_params(m_env, const_name(fn));
                expr candidate = mk_app(fn, num_params, args.data());
                collected_locals collected_ls;
                collect_non_param_locals(candidate, collected_ls);
                buffer<expr> const & locals = collected_ls.get_collected();
                if (locals.size() == m_locals_in_nested_occ.size()
                    && matches_nested_occ_upto_locals(candidate, locals)) {
                    return mk_app(mk_app(m_replacement, locals), args.size() - num_params, args.data() + num_params);
                } else {
                    for (unsigned i = 0; i < num_params; ++i) {
                        args[i] = replace_nested_occs(args[i]);
                    }
                    return copy_tag(e, mk_app(fn, args));
                }
            } else {
                return e;
            }
        }
        case expr_kind::Let:
            // whnf unfolds let-expressions
            lean_unreachable();
        }
        lean_unreachable();
    }

    expr replace_ind_types(expr const & e) {
        return replace_locals(e, m_nested_decl.get_inds().size(), m_nested_decl.get_inds().data(), m_inner_decl.get_inds().data() + 1);
    }

    void translate_nested_decl() {
        for (expr const & ind : m_nested_decl.get_inds()) {
            expr old_ind_type = mlocal_type(ind);
            name new_ind_name = mk_prefix() + mlocal_name(ind);
            expr new_ind_type = replace_nested_occs(old_ind_type);
            m_inner_decl.get_inds().push_back(mk_local(new_ind_name, new_ind_type));
            lean_trace(name({"inductive_compiler", "nested", "inner_ind"}),
                       tout() << new_ind_name << " : " << new_ind_type << "\n";);
        }
        for (expr & ir : m_inner_decl.get_intro_rules()[0]) {
            lean_trace(name({"inductive_compiler", "nested", "mimic_ir"}),
                       tout() << "before replacing ind_types: " << mlocal_name(ir) << " : " << mlocal_type(ir) << "\n";);
            ir = replace_ind_types(ir);
            lean_trace(name({"inductive_compiler", "nested", "mimic_ir"}),
                       tout() << "after replacing ind_types: " << mlocal_name(ir) << " : " << mlocal_type(ir) << "\n";);
        }
        for (buffer<expr> const & irs : m_nested_decl.get_intro_rules()) {
            m_inner_decl.get_intro_rules().emplace_back();
            for (expr const & ir : irs) {
                expr old_ir_type = mlocal_type(ir);
                name new_ir_name = mk_prefix() + mlocal_name(ir);
                expr new_ir_type = replace_ind_types(replace_nested_occs(old_ir_type));
                m_inner_decl.get_intro_rules().back().push_back(mk_local(new_ir_name, new_ir_type));
                lean_trace(name({"inductive_compiler", "nested", "inner_ir"}),
                           tout() << new_ir_name << " : " << new_ir_type << "\n";);
            }
        }
    }

    void define_nested_inds() {
        for (unsigned i = 0; i < m_nested_decl.get_inds().size(); ++i) {
            expr const & ind = m_nested_decl.get_inds()[i];
            expr new_ind_type = Pi(m_nested_decl.get_params(), mlocal_type(ind));
            expr new_ind_val = Fun(m_nested_decl.get_params(), mk_app(mk_constant(mlocal_name(m_inner_decl.get_inds()[i+1]),
                                                                                  param_names_to_levels(to_list(m_nested_decl.get_lp_names()))),
                                                                      m_nested_decl.get_params()));
            lean_trace(name({"inductive_compiler", "nested", "nested_ind"}),
                       tout() << mlocal_name(ind) << " : " << new_ind_type << " :=\n  " << new_ind_val << "\n";);

            lean_assert(!has_local(new_ind_type));
            lean_assert(!has_local(new_ind_val));
            m_env = module::add(m_env, check(m_env, mk_definition(m_env, mlocal_name(ind), to_list(m_nested_decl.get_lp_names()), new_ind_type, new_ind_val)));
        }
    }

    void construct_translator_for_nested_occ() {
        // Locals: [n1:nat]
        // Occ: vector (foo3 A (f n1))
        // Indices: [n2:nat]
        // Goal: Pi <locals>, Pi <indices>, Occ -> (one layer down)

        buffer<expr> args;
        expr fn = get_app_args(m_nested_occ, args);
        lean_assert(is_constant(fn));

        expr remaining_type = m_tctx.relaxed_whnf(m_tctx.infer(m_nested_occ));
        bool has_dep_elim = inductive::has_dep_elim(m_env, const_name(fn));

        list<level> elim_levels = const_levels(fn);
        declaration d = m_env.get(inductive::get_elim_name(const_name(fn)));
        if (length(elim_levels) < d.get_num_univ_params()) {
            lean_assert(length(elim_levels) + 1 == d.get_num_univ_params());
            elim_levels = list<level>(sort_level(get_ind_result_type(m_tctx, m_inner_decl.get_inds()[0])), elim_levels);
        }

        // Recursor takes:
        // 1. params
        // 2. motive
        // 3. minor premises
        // and yields: Pi <indices> (x : _), motive x

        // 1. params
        // (same as args)
        // (foo₃ A (f n₁))

        // 2. motive
        // (λ (n₂ : nat) (v : vector (foo₃ A (f n₁)) n₂), fvector₂ A n₁ n₂)
        expr C;
        {
            C = mk_constant(mlocal_name(m_inner_decl.get_inds()[0]), param_names_to_levels(to_list(m_nested_decl.get_lp_names())));
            C = mk_app(C, m_nested_decl.get_params());
            C = mk_app(C, m_locals_in_nested_occ);

            expr ty = remaining_type;
            buffer<expr> locals;
            while (is_pi(ty)) {
                expr l = mk_local_for(ty);
                locals.push_back(l);
                C = mk_app(C, l);
                ty = instantiate(binding_body(ty), l);
                ty = m_tctx.relaxed_whnf(ty);
            }
            if (has_dep_elim) {
                expr ignore = mk_local_pp("x_ignore", mk_app(m_nested_occ, locals));
                locals.push_back(ignore);
            }

            C = Fun(locals, C);

            lean_trace(name({"inductive_compiler", "nested", "translate"}),
                       tout() << "motive: " << C << "\n";);
        }

        // 3. minor premises
        // (λ (n₂ : nat)
        //    (x : foo₃ A (f n₁))
        //    (vs : vector (foo₃ A (f n₁)) n₂)
        //    (fvs : fvector₂ A n₁ n₂),
        //      @fvector.vcons A n₁ n₂ x fvs)
        buffer<expr> minor_premises;
        optional<list<name> > intro_rules = get_ginductive_intro_rules(m_env, const_name(fn));
        unsigned num_params = get_ginductive_num_params(m_env, const_name(fn));
        lean_assert(intro_rules);
        for (name const & intro_rule : *intro_rules) {
            // constructor vector.vcons : Π {A : Type} (n : ℕ), A → vector A n → vector A (n + 1)
            declaration d = m_env.get(intro_rule);
            expr ir_type = m_tctx.relaxed_whnf(instantiate_type_univ_params(d, const_levels(fn))); //param_names_to_levels(to_list(m_nested_decl.get_lp_names()))));

            // new constant
            expr new_ind = mk_constant(mlocal_name(m_inner_decl.get_inds()[0]),
                                       param_names_to_levels(to_list(m_nested_decl.get_lp_names())));
            new_ind = mk_app(new_ind, m_nested_decl.get_params());
            new_ind = mk_app(new_ind, m_locals_in_nested_occ);

            for (expr const & arg : args)
                ir_type = m_tctx.relaxed_whnf(instantiate(binding_body(ir_type), arg));
            // now we are at Π (n2 : ℕ), foo A (f n1) → vector (foo A (f n1)) n2 → vector (foo A (f n1)) (n2 + 1)
            buffer<expr> locals;
            buffer<expr> rec_args;
            buffer<expr> return_args;
            while (is_pi(ir_type)) {
                buffer<expr> arg_args;
                expr arg_fn = get_app_args(binding_domain(ir_type), arg_args);

                expr l = mk_local_for(ir_type);
                locals.push_back(l);
                ir_type = m_tctx.relaxed_whnf(instantiate(binding_body(ir_type), l));
                if (arg_fn == fn) {
                    // it is a recursive argument
                    expr rec_arg_type = mk_app(new_ind, arg_args.size() - num_params, arg_args.data() + num_params);
                    expr l2 = mk_local_pp("x", rec_arg_type);
                    rec_args.push_back(l2);
                    return_args.push_back(l2);
                } else {
                    return_args.push_back(l);
                }
            }
            locals.append(rec_args);
            // now locals contains all the arguments we are going to extract
            // it remains to provide the return value
            expr return_value = mk_constant(mlocal_name(m_inner_decl.get_intro_rules()[0][minor_premises.size()]),
                                            param_names_to_levels(to_list(m_nested_decl.get_lp_names())));
            return_value = mk_app(return_value, m_nested_decl.get_params());
            return_value = mk_app(return_value, m_locals_in_nested_occ);
            return_value = mk_app(return_value, return_args);
            return_value = Fun(locals, return_value);
            minor_premises.push_back(return_value);
            lean_trace(name({"inductive_compiler", "nested", "translate"}),
                       tout() << "minor premise: " << return_value << "\n";);
        }

        // TODO(dhs): what if the recursor doesn't take an extra level?
        // (i.e. where do I
        m_translator = Fun(m_locals_in_nested_occ,
                           mk_app(mk_app(mk_app(mk_constant(inductive::get_elim_name(const_name(fn)),
                                                            elim_levels),
                                                args),
                                         C),
                                  minor_premises));
        lean_trace(name({"inductive_compiler", "nested", "translate"}),
                   tout() << "type: " << m_tctx.infer(m_translator) << "\n";);
    }

    expr synthesize_translator_for_nested_occ(expr const & ty, buffer<expr> const & locals) {
        lean_trace(name({"inductive_compiler", "nested", "translate"}),
                   tout() << "(" << locals.size() << ") : " << ty << "\n";);
        // We have `vector (foo3 A (f n1)) (g n2)` and we want `foo_vector A n1 (g n2)`
        // definition vector_foo_to_foo_vector (A : Type) (n₁ : nat) :
        //   Pi (n₂ : nat), vector (@foo A (f n₁)) n₂ -> @foo_vector A n₁ n₂
        buffer<expr> args;
        expr fn = get_app_args(ty, args);
        lean_assert(is_constant(fn));
        unsigned num_params = get_ginductive_num_params(m_env, const_name(fn));
        return mk_app(mk_app(m_translator, locals),
                      args.size() - num_params,
                      args.data() + num_params);
    }

    expr synthesize_translator_for_recursive_occ(expr const & ty, buffer<optional<expr> > const & synthesized_translators) {
        lean_trace(name({"inductive_compiler", "nested", "translate"}),
                   tout() << ty << "\n";);
        buffer<expr> args;
        expr fn = get_app_args(ty, args);
        // TODO(dhs): there will be a ton of duplication for now, refactor later
        lean_assert(is_constant(fn));

        unsigned num_params = get_ginductive_num_params(m_env, const_name(fn));
        lean_assert(num_params == synthesized_translators.size());
        buffer<expr> params;
        buffer<expr> new_params;
        for (unsigned i = 0; i < synthesized_translators.size(); ++i) {
            params.push_back(args[i]);
            optional<expr> const & strans = synthesized_translators[i];
            if (strans) {
                new_params.push_back(m_tctx.whnf(binding_body(m_tctx.infer(*strans))));
            } else {
                new_params.push_back(args[i]);
            }
        }

        expr new_ind = mk_app(fn, new_params);

        expr remaining_type = m_tctx.relaxed_whnf(m_tctx.infer(mk_app(fn, params)));
        bool has_dep_elim = inductive::has_dep_elim(m_env, const_name(fn));

        list<level> elim_levels = const_levels(fn);
        declaration d = m_env.get(inductive::get_elim_name(const_name(fn)));
        if (length(elim_levels) < d.get_num_univ_params()) {
            lean_assert(length(elim_levels) + 1 == d.get_num_univ_params());
            elim_levels = list<level>(sort_level(get_ind_result_type(m_tctx, m_inner_decl.get_inds()[0])), elim_levels);
        }

        expr C;
        {
            C = fn;
            C = mk_app(C, new_params);

            expr ty = remaining_type;
            buffer<expr> locals;
            while (is_pi(ty)) {
                expr l = mk_local_for(ty);
                locals.push_back(l);
                C = mk_app(C, l);
                ty = instantiate(binding_body(ty), l);
                ty = m_tctx.relaxed_whnf(ty);
            }
            if (has_dep_elim) {
                expr ignore = mk_local_pp("x_ignore", mk_app(mk_app(fn, params), locals));
                locals.push_back(ignore);
            }

            C = Fun(locals, C);
            lean_trace(name({"inductive_compiler", "nested", "translate"}),
                       tout() << "rec_motive: " << C << "\n";);
        }

        // 3. minor premises
        // definition lvector_vector_to_lvector_fvector (A : Type) (n₁ : nat) : Pi (n₂ : nat), lvector (vector (foo A (f n₁)) (g n₁)) n₂ -> lvector (fvector A n₁ (g n₁)) n₂ :=
        // [for lvector.cons]
        // (λ (n₂ : nat)
        //    (x : vector (foo A (f n₁)) (g n₁))
        //    (lv : lvector (vector (foo A (f n₁)) (g n₁)) n₂)
        //    (lv' : lvector (fvector A n₁ (g n₁)) n₂),
        //    (@lvector.lcons (fvector A n₁ (g n₁)) n₂ (vector_to_fvector A n₁ (g n₁) x) lv'))
        buffer<expr> minor_premises;
        optional<list<name> > intro_rules = get_ginductive_intro_rules(m_env, const_name(fn));
        lean_assert(intro_rules);
        for (name const & intro_rule : *intro_rules) {
            // constructor lvector.vcons : Π {A : Type} (n : ℕ), A → lvector A n → lvector A (n + 1)
            declaration d = m_env.get(intro_rule);

            expr old_ir = mk_app(mk_constant(intro_rule, const_levels(fn)), params);
            expr new_ir = mk_app(mk_constant(intro_rule, const_levels(fn)), new_params);

            expr ir_type = m_tctx.relaxed_whnf(m_tctx.infer(old_ir));

            // Now we need to translate the arguments one by one
            buffer<expr> locals;
            buffer<expr> rec_args;
            buffer<expr> return_args;
            while (is_pi(ir_type)) {
                buffer<expr> arg_args;
                expr arg_fn = get_app_args(binding_domain(ir_type), arg_args);
                expr l = mk_local_for(ir_type);
                locals.push_back(l);
                // it may be a nested-argument
                if (arg_fn == fn && mk_app(arg_fn, num_params, arg_args.data()) == mk_app(fn, num_params, args.data())) {
                    // it is a recursive argument
                    expr rec_arg_type = mk_app(new_ind, arg_args.size() - num_params, arg_args.data() + num_params);
                    expr l2 = mk_local_pp("x", rec_arg_type);
                    rec_args.push_back(l2);
                    return_args.push_back(l2);
                } else {
                    if (auto strans = synthesize_translator_for_ir_inner_arg(binding_domain(ir_type))) {
                        return_args.push_back(mk_app(*strans, l));
                    } else {
                        return_args.push_back(l);
                    }
                }
                ir_type = m_tctx.relaxed_whnf(instantiate(binding_body(ir_type), l));
            }

            locals.append(rec_args);

            // now locals contains all the arguments we are going to extract
            // it remains to provide the return value
            expr return_value = Fun(locals, mk_app(new_ir, return_args));
            minor_premises.push_back(return_value);
            lean_trace(name({"inductive_compiler", "nested", "translate"}),
                       tout() << "minor premise: " << return_value << "\n";);
        }

        expr strans = mk_app(mk_app(mk_app(mk_constant(inductive::get_elim_name(const_name(fn)),
                                                       elim_levels),
                                           params),
                                    C),
                             minor_premises);
        expr return_value = mk_app(strans, args.size() - num_params, args.data() + num_params);

        lean_trace(name({"inductive_compiler", "nested", "translate"}),
                   tout() << "type of rec app: " << m_tctx.infer(return_value) << "\n";);
        return return_value;

    }

    void compute_local_to_constant_map() {
        for (expr const & ind : m_nested_decl.get_inds()) {
            m_ind_ir_locals.push_back(ind);
            m_ind_ir_cs.push_back(mk_app(mk_constant(mlocal_name(ind), param_names_to_levels(to_list(m_nested_decl.get_lp_names()))),
                                         m_nested_decl.get_params()));
        }
        for (expr const & ind : m_inner_decl.get_inds()) {
            m_ind_ir_locals.push_back(ind);
            m_ind_ir_cs.push_back(mk_app(mk_constant(mlocal_name(ind), param_names_to_levels(to_list(m_nested_decl.get_lp_names()))),
                                         m_nested_decl.get_params()));
        }

        for (buffer<expr> const & irs : m_nested_decl.get_intro_rules()) {
            for (expr const & ir : irs) {
                m_ind_ir_locals.push_back(ir);
                m_ind_ir_cs.push_back(mk_app(mk_constant(mlocal_name(ir), param_names_to_levels(to_list(m_nested_decl.get_lp_names()))),
                                             m_nested_decl.get_params()));
            }
        }
        for (buffer<expr> const & irs : m_inner_decl.get_intro_rules()) {
            for (expr const & ir : irs) {
                m_ind_ir_locals.push_back(ir);
                m_ind_ir_cs.push_back(mk_app(mk_constant(mlocal_name(ir), param_names_to_levels(to_list(m_nested_decl.get_lp_names()))),
                                             m_nested_decl.get_params()));
            }
        }
    }

    expr convert_locals_to_constants(expr const & e) {
        return replace_locals(e, m_ind_ir_locals, m_ind_ir_cs);
    }

    optional<expr> synthesize_translator_for_ir_inner_arg(expr const & ty) {
        // This will be called on list (list foo))
        // The goal is to return a function `f : list (list foo) -> list foo_list`.

        buffer<expr> args;
        expr fn = get_app_args(ty, args);
        if (!is_constant(fn) || !is_ginductive(m_env, const_name(fn)))
            return none_expr();

        unsigned num_params = get_ginductive_num_params(m_env, const_name(fn));

        // First we see if we are already at a nested occurrence
        expr candidate = mk_app(fn, num_params, args.data());
        collected_locals collected_ls;
        collect_non_param_locals(candidate, collected_ls);
        buffer<expr> const & locals = collected_ls.get_collected();

        if (locals.size() == m_locals_in_nested_occ.size()
            && matches_nested_occ_upto_locals(candidate, locals)) {
            // If we have found a match, then we translate the nested occurrence
            // i.e. we return `list_foo_to_foo_list inner_arg`
            return some_expr(synthesize_translator_for_nested_occ(ty, locals));
        }

        bool success = false;
        buffer<optional<expr> > synthesized_translators;
        // Otherwise, inner_arg may still have a nested occurrence inside
        for (unsigned i = 0; i < num_params; ++i) {
            // If inner_arg : list (list foo), then by induction we can convert an element of type
            // list_foo to foo_list. We want to synthesize a function `f : list foo -> foo_list`.
            // Then we can use that function in a list induction to convert
            // For each parameter argument, we still has type `list (list foo)`
            auto f = synthesize_translator_for_ir_inner_arg(args[i]);
            synthesized_translators.push_back(f);
            if (f)
                success = true;
        }
        if (!success)
            return none_expr();

        return some_expr(synthesize_translator_for_recursive_occ(ty, synthesized_translators));
    }

    optional<expr> translate_ir_arg(expr const & arg) {
        // For foo.mk : Pi (n : nat), (nat -> list foo) -> foo
        // This would be called on a local (arg : nat -> list foo)
        // It tries to return a term containing `arg` that has the un-nested type (nat -> foo_list)
        // Lambda (n:nat), list_to_foo_list (arg n)

        expr ty = m_tctx.relaxed_whnf(m_tctx.infer(arg));
        if (!has_ind_occ(ty))
            return none_expr();

        buffer<expr> locals;
        buffer<expr> inner_args;

        while (is_pi(ty)) {
            expr l = mk_local_for(ty);
            locals.push_back(l);
            ty = instantiate(binding_body(ty), l);
            ty = m_tctx.relaxed_whnf(ty);
        }
        expr arg_val = mk_app(arg, locals);
        // Now arg_val has type ty
        if (auto inner_arg_fn = synthesize_translator_for_ir_inner_arg(ty)) {
            // inner_arg_fn : inner_arg_type -> new_inner_arg_type
            // We want to return a function PACK : Pi <locals>, inner_arg_type -> Pi <locals>, new_inner_arg_type
            /*
              definition pack : (bool -> list foo) -> (bool -> foo_list) :=
              λ (f : bool -> list foo),
                λ (b : bool),
                  @list.rec foo (λ (x_ignore : list foo), foo_list) foo_list.nil
                    (λ (a : foo) (a_1 : list foo) (x : foo_list), foo_list.cons a x)
                      (f b)
            */
            expr pack_fn_val = Fun(m_nested_decl.get_params(), convert_locals_to_constants(Fun(arg, Fun(locals, mk_app(*inner_arg_fn, arg_val)))));
            expr pack_fn_type = m_tctx.infer(pack_fn_val);
            // TODO(dhs): put the name of the ind type in the name
            name pack_fn_name = "pack" + mk_fresh_name();
            lean_assert(!has_local(pack_fn_type));
            lean_assert(!has_local(pack_fn_val));

            m_env = module::add(m_env, check(m_env, mk_definition(m_env, pack_fn_name, to_list(m_nested_decl.get_lp_names()), pack_fn_type, pack_fn_val)));
            m_env = set_reducible(m_env, pack_fn_name, reducible_status::Irreducible, true);

            expr pack_fn_const = mk_constant(pack_fn_name, param_names_to_levels(to_list(m_nested_decl.get_lp_names())));
            return some_expr(mk_app(mk_app(pack_fn_const, m_nested_decl.get_params()), arg));
        } else {
            return none_expr();
        }
    }

    void define_nested_ir(unsigned ind_idx, unsigned ir_idx) {
        expr const & ir = m_nested_decl.get_intro_rules()[ind_idx][ir_idx];
        name const ir_name = mlocal_name(ir);

        // The type of the introduction rule is the one that is given
        // We need to create the _value_ here
        buffer<expr> locals;
        buffer<expr> inner_args;

        expr ty = m_tctx.relaxed_whnf(mlocal_type(ir));

        while (is_pi(ty)) {
            expr l = mk_local_for(ty);
            locals.push_back(l);
            if (auto inner_arg = translate_ir_arg(l)) {
                inner_args.push_back(*inner_arg);
            } else {
                inner_args.push_back(l);
            }
            ty = instantiate(binding_body(ty), l);
            ty = m_tctx.relaxed_whnf(ty);
        }
        expr inner_fn = mk_app(mk_constant(mlocal_name(m_inner_decl.get_intro_rules()[ind_idx+1][ir_idx]), param_names_to_levels(to_list(m_nested_decl.get_lp_names()))),
                               m_nested_decl.get_params());

        expr new_ir_val  = Fun(m_nested_decl.get_params(), convert_locals_to_constants(Fun(locals, mk_app(inner_fn, inner_args))));
        expr new_ir_type = Pi(m_nested_decl.get_params(), convert_locals_to_constants(mlocal_type(ir)));
        lean_trace(name({"inductive_compiler", "nested", "nested_ir"}),
                   tout() << mlocal_name(ir) << " : " << new_ir_type << " :=\n  " << new_ir_val << "\n";);

        implicit_infer_kind k = get_implicit_infer_kind(m_implicit_infer_map, mlocal_name(ir));
        new_ir_type = infer_implicit_params(new_ir_type, m_nested_decl.get_params().size(), k);
        lean_assert(!has_local(new_ir_type));
        lean_assert(!has_local(new_ir_val));
        m_env = module::add(m_env, check(m_env, mk_definition(m_env, mlocal_name(ir), to_list(m_nested_decl.get_lp_names()), new_ir_type, new_ir_val)));
    }

    void define_nested_irs() {
        for (unsigned ind_idx = 0; ind_idx < m_nested_decl.get_inds().size(); ++ind_idx) {
            for (unsigned ir_idx = 0; ir_idx < m_nested_decl.get_intro_rules()[ind_idx].size(); ++ir_idx)
                define_nested_ir(ind_idx, ir_idx);
        }
    }

public:
    add_nested_inductive_decl_fn(environment const & env, options const & opts,
                                 name_map<implicit_infer_kind> const & implicit_infer_map, ginductive_decl const & nested_decl):
        m_env(env), m_opts(opts), m_implicit_infer_map(implicit_infer_map),
        m_nested_decl(nested_decl), m_inner_decl(m_nested_decl.get_lp_names(), m_nested_decl.get_params()),
        m_prefix(name::mk_internal_unique_name()),
        m_tctx(env) {}

    optional<environment> operator()() {
        if (!find_nested_occ())
            return optional<environment>();
        translate_nested_decl();
        m_env = add_inner_inductive_declaration(m_env, m_opts, m_implicit_infer_map, m_inner_decl);
        compute_local_to_constant_map();
        construct_translator_for_nested_occ();
        define_nested_inds();
        define_nested_irs();

        // TODO(dhs): constructions
        return optional<environment>(m_env);
    }

};

optional<environment> add_nested_inductive_decl(environment const & env, options const & opts,
                                                name_map<implicit_infer_kind> const & implicit_infer_map, ginductive_decl const & decl) {
    return add_nested_inductive_decl_fn(env, opts, implicit_infer_map, decl)();
}

void initialize_inductive_compiler_nested() {
    register_trace_class(name({"inductive_compiler", "nested"}));
    register_trace_class(name({"inductive_compiler", "nested", "found_occ"}));
    register_trace_class(name({"inductive_compiler", "nested", "mimic_ind"}));
    register_trace_class(name({"inductive_compiler", "nested", "mimic_ir"}));
    register_trace_class(name({"inductive_compiler", "nested", "inner_ind"}));
    register_trace_class(name({"inductive_compiler", "nested", "inner_ir"}));
    register_trace_class(name({"inductive_compiler", "nested", "nested_ind"}));
    register_trace_class(name({"inductive_compiler", "nested", "nested_ir"}));
    register_trace_class(name({"inductive_compiler", "nested", "translate"}));
    g_nested_prefix = new name(name::mk_internal_unique_name());
}

void finalize_inductive_compiler_nested() {
    delete g_nested_prefix;
}
}
