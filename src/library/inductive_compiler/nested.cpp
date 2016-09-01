/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include <string>
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

static unsigned g_next_nest_id = 0;
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
    level                         m_nested_occ_level;
    levels                        m_nested_occ_ind_levels;
    buffer<expr>                  m_replacement_intro_rules;

    buffer<expr>                  m_ind_ir_locals;
    buffer<expr>                  m_ind_ir_cs;

    struct pack_info {
        unsigned ind_idx, ir_idx, arg_idx;
        name pack_name;
        name unpack_name;
        name unpack_pack_name;

        unsigned m_hash;

        pack_info(unsigned ind, unsigned ir, unsigned arg):
            ind_idx(ind), ir_idx(ir), arg_idx(arg),
            m_hash(hash(ind_idx, hash(ir_idx, arg_idx))) {}

        pack_info(unsigned ind, unsigned ir, unsigned arg,
                  name const & pack, name const & unpack, name const & unpack_pack):
            ind_idx(ind), ir_idx(ir), arg_idx(arg),
            pack_name(pack), unpack_name(unpack), unpack_pack_name(unpack_pack),
            m_hash(hash(ind_idx, hash(ir_idx, arg_idx))) {}
    };

    struct pack_info_hash_fn {
        unsigned operator()(pack_info const & k) const { return k.m_hash; }
    };

    struct pack_info_eq_fn {
        bool operator()(pack_info const & k1, pack_info const & k2) const {
            return k1.ind_idx == k2.ind_idx && k1.ir_idx == k2.ir_idx && k1.arg_idx == k2.arg_idx;
        }
    };

    typedef std::unordered_set<pack_info, pack_info_hash_fn, pack_info_eq_fn> pack_infos;

    pack_infos                   m_pack_infos;

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

    expr convert_constants_to_locals(expr const & e) {
        return replace(e, [&](expr const & e) {
                buffer<expr> args;
                expr fn = get_app_args(e, args);
                if (!is_constant(fn))
                    return none_expr();

                for (expr const & ind : m_nested_decl.get_inds()) {
                    if (const_name(fn) == mlocal_name(ind)) {
                        unsigned num_params = m_nested_decl.get_num_params();
                        return some_expr(mk_app(ind, args.size() - num_params, args.data() + num_params));
                    }
                }

                for (expr const & ind : m_inner_decl.get_inds()) {
                    if (const_name(fn) == mlocal_name(ind)) {
                        unsigned num_params = m_inner_decl.get_num_params();
                        return some_expr(mk_app(ind, args.size() - num_params, args.data() + num_params));
                    }
                }

                for (unsigned ind_idx = 0; ind_idx < m_nested_decl.get_intro_rules().size(); ++ind_idx) {
                    buffer<expr> const & irs = m_nested_decl.get_intro_rules()[ind_idx];
                    for (unsigned ir_idx = 0; ir_idx < irs.size(); ++ir_idx) {
                        expr const & ir = irs[ir_idx];
                        if (const_name(fn) == mlocal_name(ir)) {
                            unsigned num_params = m_nested_decl.get_num_params();
                            return some_expr(mk_app(ir, args.size() - num_params, args.data() + num_params));
                        }
                    }
                }

                for (unsigned ind_idx = 0; ind_idx < m_inner_decl.get_intro_rules().size(); ++ind_idx) {
                    buffer<expr> const & irs = m_inner_decl.get_intro_rules()[ind_idx];
                    for (unsigned ir_idx = 0; ir_idx < irs.size(); ++ir_idx) {
                        expr const & ir = irs[ir_idx];
                        if (const_name(fn) == mlocal_name(ir)) {
                            unsigned num_params = m_inner_decl.get_num_params();
                            return some_expr(mk_app(ir, args.size() - num_params, args.data() + num_params));
                        }
                    }
                }
                return none_expr();
            });
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

        optional<list<name> > old_intro_rules = get_ginductive_intro_rules(m_env, const_name(fn));
        lean_assert(old_intro_rules);
        for (name const & old_ir_name : *old_intro_rules) {
            expr old_ir_type = m_tctx.infer(mk_app(mk_constant(old_ir_name, const_levels(fn)), num_params, args.data()));
            name mimic_ir_name = mk_prefix() + old_ir_name;
            expr mimic_ir_type = Pi(m_locals_in_nested_occ, old_ir_type);
            m_replacement_intro_rules.push_back(mk_local(mimic_ir_name, mimic_ir_type));
        }
    }

    expr mk_local_for(expr const & b) { return mk_local(mk_fresh_name(), binding_name(b), binding_domain(b), binding_info(b)); }
    expr mk_local_for(expr const & b, name const & n) { return mk_local(mk_fresh_name(), n, binding_domain(b), binding_info(b)); }
    expr mk_local_pp(name const & n, expr const & ty) { return mk_local(mk_fresh_name(), n, ty, binder_info()); }

    bool find_nested_occ_in_ir_arg_type_core(expr const & ty, optional<expr> outer_app, unsigned num_params = 0) {
        buffer<expr> args;
        expr fn = get_app_args(ty, args);

        if (!outer_app && is_ind(fn))
            return false;

        if (outer_app && is_ind(fn)) {
            buffer<expr> outer_args;
            expr outer_fn = get_app_args(*outer_app, outer_args);

            buffer<expr> params, indices;
            split_params_indices(outer_args, num_params, params, indices);

            // we found a nested occurrence
            collected_locals collected_ls;
            collect_non_param_locals(mk_app(outer_fn, params), collected_ls);
            m_nested_occ = mk_app(outer_fn, params);
            m_nested_occ_level = get_level(m_tctx, mk_app(outer_fn, outer_args));
            m_nested_occ_ind_levels = const_levels(outer_fn);

            m_locals_in_nested_occ.append(collected_ls.get_collected());
            lean_trace(name({"inductive_compiler", "nested", "found_occ"}), tout()
                       << "(" << m_locals_in_nested_occ.size() << ") " << m_nested_occ << "\n";);
            compute_mimic_ind();
            return true;
        }

        if (is_constant(fn) && is_ginductive(m_env, const_name(fn))) {
            unsigned num_params = get_ginductive_num_params(m_env, const_name(fn));
            for (unsigned i = 0; i < num_params; ++i) {
                if (find_nested_occ_in_ir_arg_type_core(m_tctx.relaxed_whnf(args[i]), some_expr(ty), num_params))
                    return true;
            }
            throw exception("inductive type being declared cannot occur as an index argument of another inductive type");
        }
        lean_trace(name({"inductive_compiler", "nested", "found_occ"}), tout()
                   << "illegal occurrence: " << ty << "\n";);

        if (has_ind_occ(ty))
            throw exception("inductive type being declared can only be nested inside the parameters of other inductive types");
        else
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
        return locals.size() == m_locals_in_nested_occ.size()
            && replace_locals(e, locals, m_locals_in_nested_occ) == m_nested_occ;
    }

    expr replace_ind_types(expr const & e) {
        return replace_locals(e, m_nested_decl.get_inds().size(), m_nested_decl.get_inds().data(), m_inner_decl.get_inds().data() + 1);
    }

    void translate_nested_decl() {
        for (expr const & ind : m_nested_decl.get_inds()) {
            expr old_ind_type = mlocal_type(ind);
            name new_ind_name = mk_prefix() + mlocal_name(ind);
            expr new_ind_type = pack_type(old_ind_type);
            m_inner_decl.get_inds().push_back(mk_local(new_ind_name, new_ind_type));
            lean_trace(name({"inductive_compiler", "nested", "inner_ind"}),
                       tout() << new_ind_name << " : " << new_ind_type << "\n";);
        }

        m_inner_decl.get_inds().push_back(m_replacement);

        for (buffer<expr> const & irs : m_nested_decl.get_intro_rules()) {
            m_inner_decl.get_intro_rules().emplace_back();
            for (expr const & ir : irs) {
                expr old_ir_type = mlocal_type(ir);
                name new_ir_name = mk_prefix() + mlocal_name(ir);
                lean_trace(name({"inductive_compiler", "nested", "inner_ir"}),
                           tout() << "before packing type: " << new_ir_name << " : " << old_ir_type << "\n";);
                expr new_ir_type = pack_type(old_ir_type);
                lean_trace(name({"inductive_compiler", "nested", "inner_ir"}),
                           tout() << "after packing type: " << new_ir_name << " : " << new_ir_type << "\n";);
                m_inner_decl.get_intro_rules().back().push_back(mk_local(new_ir_name, new_ir_type));
            }
        }

        m_inner_decl.get_intro_rules().emplace_back();
        for (unsigned ir_idx = 0; ir_idx < m_replacement_intro_rules.size(); ++ir_idx) {
            expr & ir = m_replacement_intro_rules[ir_idx];
            lean_trace(name({"inductive_compiler", "nested", "mimic_ir"}),
                       tout() << "before packing type: " << mlocal_name(ir) << " : " << mlocal_type(ir) << "\n";);
            expr new_ir_type = pack_type(mlocal_type(ir));
            ir = update_mlocal(ir, new_ir_type);
            m_inner_decl.get_intro_rules().back().push_back(ir);
            lean_trace(name({"inductive_compiler", "nested", "mimic_ir"}),
                       tout() << "after packing type: " << mlocal_name(ir) << " : " << mlocal_type(ir) << "\n";);

            // Not a great place for it, but we create the pack and unpack lemmas for the mimic_irs here
            // TODO(dhs): when do we used these?
            buffer<expr> locals;
            expr ty = m_tctx.relaxed_whnf(new_ir_type);

            while (is_pi(ty)) {
                expr l = mk_local_for(ty);
                translate_ir_arg(m_nested_decl.get_inds().size(), ir_idx, locals, l);
                locals.push_back(l);
                ty = instantiate(binding_body(ty), l);
                ty = m_tctx.relaxed_whnf(ty);
            }
        }
    }

    void define_nested_inds() {
        for (unsigned i = 0; i < m_nested_decl.get_inds().size(); ++i) {
            expr const & ind = m_nested_decl.get_inds()[i];
            expr new_ind_type = Pi(m_nested_decl.get_params(), mlocal_type(ind));
            expr new_ind_val = Fun(m_nested_decl.get_params(), mk_app(mk_constant(mlocal_name(m_inner_decl.get_inds()[i]),
                                                                                  param_names_to_levels(to_list(m_nested_decl.get_lp_names()))),
                                                                      m_nested_decl.get_params()));
            lean_trace(name({"inductive_compiler", "nested", "nested_ind"}),
                       tout() << mlocal_name(ind) << " : " << new_ind_type << " :=\n  " << new_ind_val << "\n";);

            lean_assert(!has_local(new_ind_type));
            lean_assert(!has_local(new_ind_val));
            m_env = module::add(m_env, check(m_env, mk_definition(m_env, mlocal_name(ind), to_list(m_nested_decl.get_lp_names()), new_ind_type, new_ind_val)));
            m_tctx.set_env(m_env);
        }
    }

    expr pack_type(expr const & _e) {
        expr e = m_tctx.relaxed_whnf(_e);
        switch (e.kind()) {
        case expr_kind::Sort:
        case expr_kind::Constant:
            return e;
        case expr_kind::Local:
        {
            for (unsigned ind_idx = 0; ind_idx < m_nested_decl.get_num_inds(); ++ind_idx) {
                expr const & ind = m_nested_decl.get_ind(ind_idx);
                if (e == ind)
                    return m_inner_decl.get_ind(ind_idx);

                for (unsigned ir_idx = 0; ir_idx < m_nested_decl.get_num_intro_rules(ind_idx); ++ir_idx) {
                    expr const & ir = m_nested_decl.get_intro_rule(ind_idx, ir_idx);
                    if (e == ir)
                        return m_inner_decl.get_intro_rule(ind_idx, ir_idx);
                }
            }
            return e;
        }
        case expr_kind::Macro:
        {
            buffer<expr> new_args;
            unsigned nargs = macro_num_args(e);
            for (unsigned i = 0; i < nargs; i++)
                new_args.push_back(pack_type(macro_arg(e, i)));
            return update_macro(e, new_args.size(), new_args.data());
        }
        case expr_kind::Lambda:
        case expr_kind::Pi:
        {
            expr new_dom = pack_type(binding_domain(e));
            expr l = mk_local_pp("x_new_dom", new_dom);
            expr new_body = abstract_local(pack_type(instantiate(binding_body(e), l)), l);
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
                buffer<expr> const & occ_locals = collected_ls.get_collected();
                if (matches_nested_occ_upto_locals(candidate, occ_locals)) {
                    for (unsigned i = num_params; i < args.size(); ++i)
                        args[i] = pack_type(args[i]);
                    return copy_tag(e, mk_app(mk_app(m_replacement, occ_locals), args.size() - num_params, args.data() + num_params));
                }
            }
            fn = pack_type(fn);
            for (unsigned i = 0; i < args.size(); ++i) {
                args[i] = pack_type(args[i]);
            }
            return copy_tag(e, mk_app(fn, args));
        }
        case expr_kind::Var:
        case expr_kind::Meta:
        case expr_kind::Let:
            lean_unreachable();
        }
        lean_unreachable();
    }

    // Does two things: replaces nested occurrences and "lifts" introduction rules
    expr unpack_type(expr const & e) {
        return replace(e, [&](expr const & e) {
                buffer<expr> args;
                expr fn = get_app_args(e, args);

                if (!is_local(fn))
                    return none_expr();

                // 1. foo_list -> list foo
                if (fn == m_replacement && args.size() == m_locals_in_nested_occ.size()) {
                    // TODO(dhs): awkward assert
                    lean_assert(std::all_of(args.begin(), args.end(), [&](expr const & arg) { return is_local(arg) || is_var(arg); }));
                    return some_expr(copy_tag(e, nested_occ_with_locals(args)));
                }

                if (!is_local(e))
                    return none_expr();

                // 2a. <id>.foo -> foo (not necessary since they are definitionally equal)
                // 2b. <id>.foo.mk -> foo.mk
                for (unsigned ind_idx = 1; ind_idx < m_inner_decl.get_num_inds(); ++ind_idx) {
                    expr const & ind = m_inner_decl.get_ind(ind_idx);
                    if (e == ind)
                        return some_expr(m_nested_decl.get_ind(ind_idx-1));

                    for (unsigned ir_idx = 0; ir_idx < m_inner_decl.get_num_intro_rules(ind_idx); ++ir_idx) {
                        expr const & ir = m_inner_decl.get_intro_rule(ind_idx, ir_idx);
                        if (e == ir)
                            return some_expr(m_nested_decl.get_intro_rule(ind_idx-1, ir_idx));
                    }
                }
                return none_expr();
            });
    }

    optional<expr> try_pack_type(expr const & ty) {
        expr new_ty = pack_type(ty);
        if (new_ty == ty)
            return none_expr();
        else
            return some_expr(new_ty);
    }

    optional<expr> try_unpack_type(expr const & ty) {
        expr new_ty = unpack_type(ty);
        if (new_ty == ty)
            return none_expr();
        else
            return some_expr(new_ty);
    }

    expr nested_occ_with_locals(buffer<expr> const & new_locals) {
        return replace_locals(m_nested_occ, m_locals_in_nested_occ, new_locals);
    }

    expr occ_as_fun() {
        return Fun(m_locals_in_nested_occ, m_nested_occ);
    }

    void split_params_indices(buffer<expr> const & args, unsigned num_params, buffer<expr> & params, buffer<expr> & indices) {
        for (unsigned i = 0; i < num_params; ++i)
            params.push_back(args[i]);

        for (unsigned i = num_params; i < args.size(); ++i)
            indices.push_back(args[i]);
    }

    optional<expr> build_primitive_pack(expr const & ty) {
        // returns a function primitive_pack : ty -> pack_type(ty)
        buffer<expr> args;
        expr fn = get_app_args(ty, args);
        if (!is_constant(fn) || !is_ginductive(m_env, const_name(fn)))
            return none_expr();

        unsigned num_params = get_ginductive_num_params(m_env, const_name(fn));
        buffer<expr> occ_locals;

        // 1. confirm that it is indeed a nested occurrence
        {
            expr candidate = mk_app(fn, num_params, args.data());
            collected_locals collected_ls;
            collect_non_param_locals(candidate, collected_ls);
            occ_locals = collected_ls.get_collected();

            if (!matches_nested_occ_upto_locals(candidate, occ_locals))
                return none_expr();
        }

        expr nested_occ = nested_occ_with_locals(occ_locals);
        expr remaining_type = m_tctx.relaxed_whnf(m_tctx.infer(nested_occ));
        bool has_dep_elim = inductive::has_dep_elim(m_env, const_name(fn));

        buffer<expr> ind_params, ind_indices;
        split_params_indices(args, num_params, ind_params, ind_indices);

        // 2. elim levels
        list<level> elim_levels = const_levels(fn);
        declaration d = m_env.get(inductive::get_elim_name(const_name(fn)));
        if (length(elim_levels) < d.get_num_univ_params()) {
            lean_assert(length(elim_levels) + 1 == d.get_num_univ_params());
            elim_levels = list<level>(sort_level(get_ind_result_type(m_tctx, m_replacement)), elim_levels);
        }

        // 3. motive
        expr C;
        {
            C = m_replacement;
            C = mk_app(C, occ_locals);

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
                expr ignore = mk_local_pp("x_ignore", mk_app(nested_occ, locals));
                locals.push_back(ignore);
            }

            C = Fun(locals, C);

            lean_trace(name({"inductive_compiler", "nested", "translate"}),
                       tout() << "motive: " << C << "\n";);
        }

        // 4. minor premises
        buffer<expr> minor_premises;
        optional<list<name> > intro_rules = get_ginductive_intro_rules(m_env, const_name(fn));
        lean_assert(intro_rules);
        for (name const & intro_rule : *intro_rules) {
            // constructor vector.vcons : Π {A : Type} (n : ℕ), A → vector A n → vector A (n + 1)
            declaration d = m_env.get(intro_rule);
            expr ir_type = m_tctx.relaxed_whnf(instantiate_type_univ_params(d, const_levels(fn)));

            for (expr const & ind_param : ind_params) {
                lean_assert(is_pi(ir_type));
                ir_type = m_tctx.relaxed_whnf(instantiate(binding_body(ir_type), ind_param));
            }
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
                    expr rec_arg_type = mk_app(mk_app(m_replacement, occ_locals), arg_args.size() - num_params, arg_args.data() + num_params);
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
            expr return_value = m_replacement_intro_rules[minor_premises.size()];
            return_value = mk_app(return_value, occ_locals);
            return_value = mk_app(return_value, return_args);
            return_value = Fun(locals, return_value);
            minor_premises.push_back(return_value);
            lean_trace(name({"inductive_compiler", "nested", "translate"}),
                       tout() << "minor premise: " << return_value << "\n";);
        }

        // 4. Abstracting and appling to indices
        expr pack_no_indices = mk_app(mk_app(mk_app(mk_constant(inductive::get_elim_name(const_name(fn)),
                                                                elim_levels),
                                                    ind_params),
                                             C),
                                      minor_premises);

        expr result = mk_app(pack_no_indices, ind_indices);

        lean_assert(m_tctx.is_def_eq(m_tctx.infer(result), mk_arrow(ty, pack_type(ty))));
        return some_expr(result);
    }

    optional<expr> build_primitive_unpack(expr const & ty) {
        // returns a function primitive_unpack : ty -> unpack_type(ty)
        buffer<expr> args;
        expr fn = get_app_args(ty, args);
        if (fn != m_replacement)
            return none_expr();

        buffer<expr> occ_locals, rest_indices;
        split_params_indices(args, m_locals_in_nested_occ.size(), occ_locals, rest_indices);

        expr new_ind = occ_as_fun();
        name new_ind_name = const_name(get_app_fn(m_nested_occ));
        bool has_dep_elim = inductive::has_dep_elim(m_env, new_ind_name);
        unsigned ind_num_params = get_ginductive_num_params(m_env, new_ind_name);

        buffer<expr> ind_param_fns;
        {
            get_app_args(m_nested_occ, ind_param_fns);
            ind_param_fns.shrink(ind_num_params);
            for (expr & ind_param_fn : ind_param_fns) {
                ind_param_fn = Fun(m_locals_in_nested_occ, ind_param_fn);
            }
        }

        // 2. elim levels
        list<level> elim_levels = param_names_to_levels(to_list(m_inner_decl.get_lp_names()));
        declaration d = m_env.get(inductive::get_elim_name(mlocal_name(fn)));
        if (length(elim_levels) < d.get_num_univ_params()) {
            lean_assert(length(elim_levels) + 1 == d.get_num_univ_params());
            elim_levels = list<level>(m_nested_occ_level, elim_levels);
        }

        // 3. motive
        expr C;
        {
            C = new_ind; // think "fun n, list (bar n)"

            expr ty = mlocal_type(fn);
            buffer<expr> locals;
            unsigned i = 0;
            while (is_pi(ty)) {
                expr l = mk_local_for(ty);
                locals.push_back(l);
                C = mk_app(C, l);

                ty = instantiate(binding_body(ty), l);
                ty = m_tctx.relaxed_whnf(ty);
                ++i;
            }
            if (has_dep_elim) {
                expr ignore = mk_local_pp("x_ignore", mk_app(fn, locals));
                locals.push_back(ignore);
            }

            C = Fun(locals, C);
        }

        // 4. minor premises
        buffer<expr> minor_premises;
        optional<list<name> > unpacked_intro_rules_list = get_ginductive_intro_rules(m_env, new_ind_name);
        lean_assert(unpacked_intro_rules_list);
        buffer<name> unpacked_intro_rules;
        to_buffer(*unpacked_intro_rules_list, unpacked_intro_rules);
        lean_assert(m_replacement_intro_rules.size() == unpacked_intro_rules.size());

        for (unsigned ir_idx = 0; ir_idx < unpacked_intro_rules.size(); ++ir_idx) {
            expr const & ir = m_replacement_intro_rules[ir_idx];
            name const & unpacked_intro_rule_name = unpacked_intro_rules[ir_idx];

            expr ir_type = m_tctx.relaxed_whnf(mlocal_type(ir));

            buffer<expr> locals;
            buffer<expr> rec_args;
            buffer<expr> return_args;
            unsigned i = 0;

            if (occ_locals.empty()) {
                return_args.append(ind_param_fns);
            }

            while (is_pi(ir_type)) {
                buffer<expr> arg_args;
                expr arg_fn = get_app_args(binding_domain(ir_type), arg_args);

                expr l = mk_local_for(ir_type);
                locals.push_back(l);
                ir_type = m_tctx.relaxed_whnf(instantiate(binding_body(ir_type), l));
                if (arg_fn == fn) {
                    // it is a recursive argument
                    expr rec_arg_type = mk_app(new_ind, arg_args);
                    expr l2 = mk_local_pp("x", rec_arg_type);
                    rec_args.push_back(l2);
                    return_args.push_back(l2);
                } else {
                    // TODO(dhs): confirm that I only need this check in this branch
                    if (i >= occ_locals.size())
                        return_args.push_back(l);
                }
                i++;
                if (i == occ_locals.size()) {
                    for (expr const & ind_param_fn : ind_param_fns) {
                        return_args.push_back(mk_app(ind_param_fn, locals));
                    }
                }
            }
            locals.append(rec_args);

            expr return_value = mk_constant(unpacked_intro_rule_name, m_nested_occ_ind_levels);
            return_value = mk_app(return_value, return_args);
            return_value = Fun(locals, return_value);
            minor_premises.push_back(return_value);
            lean_trace(name({"inductive_compiler", "nested", "translate"}),
                       tout() << "minor premise: " << return_value << "\n";);
        }

        // 4. Abstracting and appling to indices
        expr unpack_no_indices = mk_app(mk_app(mk_app(mk_constant(inductive::get_elim_name(mlocal_name(fn)),
                                                                  elim_levels),
                                                      m_inner_decl.get_params()),
                                               C),
                                        minor_premises);

        expr result = mk_app(mk_app(unpack_no_indices, occ_locals), rest_indices);

        expr result_type = convert_locals_to_constants(replace_ind_types(m_tctx.infer(result)));
        expr expected_type = convert_locals_to_constants(replace_ind_types(mk_arrow(ty, unpack_type(ty))));

        bool correct = m_tctx.is_def_eq(result_type, expected_type);
        lean_assert(correct);
        return some_expr(result);
    }

    optional<expr_pair> build_nested_pack_unpack(expr const & ty) {
        // returns functions
        // nested_pack : ty -> pack_type(ty)
        // nested_unpack : pack_type(ty) -> ty

        // handles nested occurrences
        if (!has_ind_occ(ty) || ty == pack_type(ty))
            return optional<expr_pair>();

        buffer<expr> args;
        expr fn = get_app_args(ty, args);

        if (!is_constant(fn) || !is_ginductive(m_env, const_name(fn)))
            return optional<expr_pair>();

        if (auto primitive_pack_fn = build_primitive_pack(ty)) {
            auto primitive_unpack_fn = build_primitive_unpack(pack_type(ty));
            lean_assert(primitive_unpack_fn);
            return optional<expr_pair>(mk_pair(*primitive_pack_fn, *primitive_unpack_fn));
        }

        unsigned num_params = get_ginductive_num_params(m_env, const_name(fn));
        buffer<expr> unpacked_params;
        buffer<expr> packed_params;
        for (unsigned i = 0; i < num_params; ++i) {
            unpacked_params.push_back(args[i]);
            packed_params.push_back(pack_type(args[i]));
        }

        expr packed_ind = mk_app(fn, packed_params);
        expr unpacked_ind = mk_app(fn, unpacked_params);

        expr remaining_unpacked_type = m_tctx.relaxed_whnf(m_tctx.infer(unpacked_ind));
        expr remaining_packed_type = m_tctx.relaxed_whnf(m_tctx.infer(packed_ind));
        lean_assert(pack_type(remaining_unpacked_type) == remaining_packed_type);

        bool has_dep_elim = inductive::has_dep_elim(m_env, const_name(fn));

        list<level> elim_levels = const_levels(fn);
        declaration d = m_env.get(inductive::get_elim_name(const_name(fn)));
        if (length(elim_levels) < d.get_num_univ_params()) {
            lean_assert(length(elim_levels) + 1 == d.get_num_univ_params());
            // Remind me: why get_ind_result_type?
            // Is it the same for both directions?
            elim_levels = list<level>(sort_level(get_ind_result_type(m_tctx, m_replacement)), elim_levels);
        }

        auto construct_C = [&](expr const & return_value, expr const & remaining_type, buffer<expr> const & params) {
            expr C = return_value;
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

            return Fun(locals, C);
        };

        expr pack_C = construct_C(packed_ind, remaining_unpacked_type, unpacked_params);
        expr unpack_C = construct_C(unpacked_ind, remaining_packed_type, packed_params);

        optional<list<name> > intro_rules = get_ginductive_intro_rules(m_env, const_name(fn));

        buffer<expr> pack_minor_premises, unpack_minor_premises;
        for (name const & intro_rule : *intro_rules) {
            declaration d = m_env.get(intro_rule);
            expr unpacked_ir = mk_app(mk_constant(intro_rule, const_levels(fn)), unpacked_params);
            expr packed_ir = mk_app(mk_constant(intro_rule, const_levels(fn)), packed_params);

            expr unpacked_ir_type = m_tctx.relaxed_whnf(m_tctx.infer(unpacked_ir));
            expr packed_ir_type = m_tctx.relaxed_whnf(m_tctx.infer(packed_ir));

            buffer<expr> pack_locals;
            buffer<expr> pack_rec_args;
            buffer<expr> pack_return_args;

            buffer<expr> unpack_rec_args;
            buffer<expr> unpack_locals;
            buffer<expr> unpack_return_args;

            while (is_pi(unpacked_ir_type) && is_pi(packed_ir_type)) {
                buffer<expr> unpacked_arg_args;
                expr unpacked_arg_fn = get_app_args(binding_domain(unpacked_ir_type), unpacked_arg_args);

                buffer<expr> packed_arg_args;
                expr packed_arg_fn = get_app_args(binding_domain(packed_ir_type), packed_arg_args);

                expr pack_l = mk_local_for(unpacked_ir_type);
                pack_locals.push_back(pack_l);

                expr unpack_l = mk_local_for(packed_ir_type);
                unpack_locals.push_back(unpack_l);

                if (unpacked_arg_fn == fn && mk_app(unpacked_arg_fn, num_params, unpacked_arg_args.data()) == unpacked_ind) {
                    // it is a recursive argument
                    expr pack_rec_arg_type = mk_app(packed_ind, unpacked_arg_args.size() - num_params, unpacked_arg_args.data() + num_params);
                    expr pack_l2 = mk_local_pp("x_pack", pack_rec_arg_type);
                    pack_rec_args.push_back(pack_l2);
                    pack_return_args.push_back(pack_l2);

                    // TODO(dhs): current spot
                    expr unpack_rec_arg_type = mk_app(unpacked_ind, packed_arg_args.size() - num_params, packed_arg_args.data() + num_params);
                    expr unpack_l2 = mk_local_pp("x_unpack", unpack_rec_arg_type);
                    unpack_rec_args.push_back(unpack_l2);
                    unpack_return_args.push_back(unpack_l2);
                } else {
                    if (auto pack_unpack_fn = build_nested_pack_unpack(m_tctx.relaxed_whnf(binding_domain(unpacked_ir_type)))) {
                        pack_return_args.push_back(mk_app(pack_unpack_fn->first, pack_l));
                        unpack_return_args.push_back(mk_app(pack_unpack_fn->second, unpack_l));
                    } else {
                        // This assert doesn't work because ind locals are not definitionally equal
                        // (even though the associated constants are)
                        // lean_assert(m_tctx.is_def_eq(mlocal_type(pack_l), mlocal_type(unpack_l)));
                        pack_return_args.push_back(pack_l);
                        unpack_return_args.push_back(unpack_l);
                    }
                }
                unpacked_ir_type = m_tctx.relaxed_whnf(instantiate(binding_body(unpacked_ir_type), pack_l));
                packed_ir_type = m_tctx.relaxed_whnf(instantiate(binding_body(packed_ir_type), unpack_l));
            }
            pack_locals.append(pack_rec_args);
            unpack_locals.append(unpack_rec_args);

            expr pack_minor_premise = Fun(pack_locals, mk_app(packed_ir, pack_return_args));
            // TODO(dhs): does this always work? Think!
            expr unpack_minor_premise = Fun(unpack_locals, mk_app(unpacked_ir, unpack_return_args));
            pack_minor_premises.push_back(pack_minor_premise);
            unpack_minor_premises.push_back(unpack_minor_premise);
        }

        // TODO(dhs): we do not want to specialize here for the indices
        // We need the more flexible theorem to even state the unpack-pack lemma when there are indices
        expr pack_fn = mk_app(mk_app(mk_app(mk_app(mk_constant(inductive::get_elim_name(const_name(fn)),
                                                               elim_levels),
                                                   unpacked_params),
                                            pack_C),
                                     pack_minor_premises),
                              args.size() - num_params, args.data() + num_params);

        expr unpack_fn = mk_app(mk_app(mk_app(mk_app(mk_constant(inductive::get_elim_name(const_name(fn)),
                                                                 elim_levels),
                                                     packed_params),
                                            unpack_C),
                                     unpack_minor_premises),
                                args.size() - num_params, args.data() + num_params);

        return optional<expr_pair>(mk_pair(pack_fn, unpack_fn));
    }

    optional<expr_pair> build_pack_unpack(expr const & _ty) {
        // returns functions:
        // pack : ty -> pack_type(ty)
        // unpack : pack_type(ty) -> ty
        // handles nested occurrences and outer pis
        expr ty = m_tctx.relaxed_whnf(_ty);
        if (!has_ind_occ(ty) || ty == pack_type(ty))
            return optional<expr_pair>();

        expr x_to_pack = mk_local_pp("x_to_pack", ty);
        expr x_to_unpack = mk_local_pp("x_to_unpack", pack_type(ty));

        buffer<expr> locals;
        buffer<expr> inner_args;

        while (is_pi(ty)) {
            expr l = mk_local_for(ty);
            locals.push_back(l);
            ty = instantiate(binding_body(ty), l);
            ty = m_tctx.relaxed_whnf(ty);
        }
        expr body_to_pack = mk_app(x_to_pack, locals);
        expr body_to_unpack = mk_app(x_to_unpack, locals);

        lean_assert(m_tctx.is_def_eq(m_tctx.infer(body_to_pack), ty));
        lean_assert(m_tctx.is_def_eq(m_tctx.infer(body_to_unpack), pack_type(ty)));

        if (auto nested_pack_unpack_fn = build_nested_pack_unpack(ty)) {
            expr const & nested_pack_fn = nested_pack_unpack_fn->first;
            expr const & nested_unpack_fn = nested_pack_unpack_fn->second;
            expr pack_fn = Fun(x_to_pack, Fun(locals, mk_app(nested_pack_fn, body_to_pack)));
            expr unpack_fn = Fun(x_to_unpack, Fun(locals, mk_app(nested_unpack_fn, body_to_unpack)));
            return optional<expr_pair>(mk_pair(pack_fn, unpack_fn));
        } else {
            return optional<expr_pair>();
        }
    }

    // Awkward design: the first two arguments are only used to index the pack info
    // compute_pack_info_for_nested_occ() calls it with ind_idx one past the end.
    optional<expr> translate_ir_arg(unsigned ind_idx, unsigned ir_idx, buffer<expr> const & previous_args, expr const & arg) {
        auto pack_unpack_fn = build_pack_unpack(mlocal_type(arg));
        if (!pack_unpack_fn)
            return none_expr();

        lean_trace(name({"inductive_compiler", "nested", "pack"}), tout() << ind_idx << ir_idx << previous_args.size() << "\n";);

        expr const & pack_fn = pack_unpack_fn->first;
        expr const & unpack_fn = pack_unpack_fn->second;

        // pack_fn :: Pi <indices>, arg_ty -> packed_type(arg_ty)
        // unpack_fn :: Pi <indices>, packed_type(arg_ty) -> arg_ty

        unsigned arg_idx = previous_args.size();
        const char * s_ir_idx = ("_" + std::to_string(ir_idx)).c_str();
        const char * s_arg_idx = ("_" + std::to_string(arg_idx)).c_str();

        expr pack_fn_val = Fun(m_nested_decl.get_params(), convert_locals_to_constants(Fun(previous_args, pack_fn)));
        expr pack_fn_type = m_tctx.infer(pack_fn_val);
        name pack_fn_name = (mlocal_name(m_nested_decl.get_ind(ind_idx)) + "pack").append_after(s_ir_idx).append_after(s_arg_idx);

        lean_assert(!has_local(pack_fn_type));
        lean_assert(!has_local(pack_fn_val));

        lean_trace(name({"inductive_compiler", "nested", "pack"}),
                   tout() << pack_fn_name << " : " << pack_fn_type << "\n";);

        m_env = module::add(m_env, check(m_env, mk_definition(m_env, pack_fn_name, to_list(m_nested_decl.get_lp_names()), pack_fn_type, pack_fn_val)));

        expr unpack_fn_val = Fun(m_nested_decl.get_params(), convert_locals_to_constants(Fun(previous_args, unpack_fn)));
        expr unpack_fn_type = m_tctx.infer(unpack_fn_val);
        name unpack_fn_name = (mlocal_name(m_nested_decl.get_ind(ind_idx)) + "unpack").append_after(s_ir_idx).append_after(s_arg_idx);


        lean_assert(!has_local(unpack_fn_type));
        lean_assert(!has_local(unpack_fn_val));

        lean_trace(name({"inductive_compiler", "nested", "unpack"}),
                   tout() << unpack_fn_name << " : " << unpack_fn_type << "\n";);

        m_env = module::add(m_env, check(m_env, mk_definition(m_env, unpack_fn_name, to_list(m_nested_decl.get_lp_names()), unpack_fn_type, unpack_fn_val)));
        m_tctx.set_env(m_env);

        levels lvls = param_names_to_levels(to_list(m_nested_decl.get_lp_names()));
        expr pack_fn_const = mk_constant(pack_fn_name, lvls);
        expr unpack_fn_const = mk_constant(unpack_fn_name, lvls);
        expr unpack_pack_id_type;
        {
            expr packed_arg = mk_local_pp("x_packed", pack_type(mlocal_type(arg)));
            expr lhs = mk_app(mk_app(mk_app(pack_fn_const, m_nested_decl.get_params()), previous_args),
                              mk_app(mk_app(mk_app(unpack_fn_const, m_nested_decl.get_params()), previous_args), packed_arg));
            unpack_pack_id_type = Pi(m_nested_decl.get_params(),
                                     convert_locals_to_constants(
                                         Pi(previous_args,
                                            Pi(packed_arg,
                                               mk_eq(m_tctx, lhs, packed_arg)))));
        }
        name unpack_pack_id_name = (mlocal_name(m_nested_decl.get_ind(ind_idx)) + "unpack_pack").append_after(s_ir_idx).append_after(s_arg_idx);

        lean_trace(name({"inductive_compiler", "nested", "unpack_pack"}),
                   tout() << unpack_pack_id_name << " : " << unpack_pack_id_type << "\n";);

        m_env = module::add(m_env, check(m_env, mk_axiom(unpack_pack_id_name, to_list(m_nested_decl.get_lp_names()), unpack_pack_id_type)));
        m_tctx.set_env(m_env);

        m_pack_infos.emplace(ind_idx, ir_idx, arg_idx, pack_fn_name, unpack_fn_name, unpack_pack_id_name);

        // TODO(dhs): this is where I create the types, call tactics, and add definitions for the inverse theorem,
        // the size-of, and the size-of preservation theorem.
        return some_expr(mk_app(mk_app(mk_app(pack_fn_const, m_nested_decl.get_params()), previous_args), arg));
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
            if (auto inner_arg = translate_ir_arg(ind_idx, ir_idx, locals, l)) {
                inner_args.push_back(*inner_arg);
            } else {
                inner_args.push_back(l);
            }
            locals.push_back(l);
            ty = instantiate(binding_body(ty), l);
            ty = m_tctx.relaxed_whnf(ty);
        }
        expr inner_fn = mk_app(mk_constant(mlocal_name(m_inner_decl.get_intro_rules()[ind_idx][ir_idx]), param_names_to_levels(to_list(m_nested_decl.get_lp_names()))),
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
        m_tctx.set_env(m_env);
    }

    void compute_pack_info_for_nested_occ() {
        // TODO(dhs): pack and unpack for the constructor types of the nested occurrence
        // (not sure what this means)
    }

    void define_nested_irs() {
        for (unsigned ind_idx = 0; ind_idx < m_nested_decl.get_inds().size(); ++ind_idx) {
            for (unsigned ir_idx = 0; ir_idx < m_nested_decl.get_intro_rules()[ind_idx].size(); ++ir_idx)
                define_nested_ir(ind_idx, ir_idx);
        }
    }

    expr introduce_locals_for_nested_recursor(unsigned ind_idx, expr const & outer_recursor_type,
                                              expr & C, buffer<expr> & minor_premises,
                                              buffer<expr> & indices, expr & major_premise) {
        expr ty = m_tctx.relaxed_whnf(outer_recursor_type);

        // We always instantiate with our stored params
        // Not sure if it is necessary here, depending on what utilities we need to call
        for (unsigned p_idx = 0; p_idx < m_nested_decl.get_num_params(); ++p_idx) {
            ty = m_tctx.relaxed_whnf(instantiate(binding_body(ty), m_nested_decl.get_param(p_idx)));
        }

        ty = convert_constants_to_locals(ty);

        C = mk_local_for(ty, "C");
        ty = m_tctx.relaxed_whnf(instantiate(binding_body(ty), C));

        for (unsigned ir_idx = 0; ir_idx < m_nested_decl.get_num_intro_rules(ind_idx); ++ir_idx) {
            expr minor_premise = mk_local_for(ty);
            minor_premises.push_back(minor_premise);
            ty = m_tctx.relaxed_whnf(instantiate(binding_body(ty), minor_premise));
        }

        while (is_pi(ty)) {
            expr l = mk_local_for(ty);
            ty = m_tctx.relaxed_whnf(instantiate(binding_body(ty), l));
            if (is_pi(ty))
                indices.push_back(l);
            else
                major_premise = l;
        }

        return ty;
    }


    class build_nested_minor_premise_fn {
        add_nested_inductive_decl_fn & m_outer;
        unsigned m_ind_idx;
        unsigned m_ir_idx;
        expr m_minor_premise;
        buffer<expr> const & m_inner_minor_premise_args;
        buffer<expr> const & m_inner_minor_premise_rec_args;

        bool m_dep_elim{false};
        expr m_motive_app;

        expr build(unsigned arg_idx, list<expr> rev_ir_args, list<expr> rev_mp_args) {
            if (arg_idx == m_inner_minor_premise_args.size()) {
                buffer<expr> mp_args;
                to_buffer(reverse(rev_mp_args), mp_args);
                return mk_app(mk_app(m_minor_premise, mp_args), m_inner_minor_premise_rec_args);
            }

            expr const & arg = m_inner_minor_premise_args[arg_idx];

            auto it = m_outer.m_pack_infos.find(pack_info(m_ind_idx, m_ir_idx, arg_idx));

            if (it == m_outer.m_pack_infos.end()) {
                return build(arg_idx+1, list<expr>(arg, rev_ir_args), list<expr>(arg, rev_mp_args));
            }

            buffer<expr> ir_args;
            to_buffer(reverse(rev_ir_args), ir_args);

            buffer<expr> mp_args;
            to_buffer(reverse(rev_mp_args), mp_args);

            // TODO(dhs): are these levels correct?
            // Should I just store the constants in the [pack_info] object?
            expr pack_fn = mk_app(mk_app(mk_constant(it->pack_name, m_outer.m_nested_decl.get_levels()),
                                         m_outer.m_nested_decl.get_params()), mp_args);
            expr unpack_fn = mk_app(mk_app(mk_constant(it->unpack_name, m_outer.m_nested_decl.get_levels()),
                                         m_outer.m_nested_decl.get_params()), mp_args);
            expr unpack_pack_fn = mk_app(mk_app(mk_constant(it->unpack_pack_name, m_outer.m_nested_decl.get_levels()),
                                         m_outer.m_nested_decl.get_params()), mp_args);

            expr motive;
            {
                if (m_dep_elim)
                    motive = Fun(m_inner_minor_premise_args[arg_idx],
                                 mk_app(m_motive_app,
                                        mk_app(
                                            mk_app(m_outer.m_inner_decl.get_intro_rule(m_ind_idx, m_ir_idx),
                                                   ir_args),
                                            m_inner_minor_premise_args.size() - arg_idx,
                                            m_inner_minor_premise_args.data() + arg_idx)));
                else
                    motive = Fun(m_inner_minor_premise_args[arg_idx], m_motive_app);
            }

            expr rest = build(arg_idx+1,
                              list<expr>(mk_app(pack_fn, mk_app(unpack_fn, arg)), rev_ir_args),
                              list<expr>(mk_app(unpack_fn, arg), rev_mp_args));
            expr equality_proof = mk_app(unpack_pack_fn, arg);

            return mk_eq_rec(m_outer.m_tctx, motive, rest, equality_proof);
        }

    public:
        build_nested_minor_premise_fn(add_nested_inductive_decl_fn & outer,
                                      unsigned ind_idx,
                                      unsigned ir_idx,
                                      expr const & minor_premise,
                                      buffer<expr> const & inner_minor_premise_args,
                                      buffer<expr> const & inner_minor_premise_rec_args,
                                      expr const & goal):
            m_outer(outer),
            m_ind_idx(ind_idx),
            m_ir_idx(ir_idx),
            m_minor_premise(minor_premise),
            m_inner_minor_premise_args(inner_minor_premise_args),
            m_inner_minor_premise_rec_args(inner_minor_premise_rec_args)
            {
                // TODO(dhs): awkward way of checking for dependent elimination
                buffer<expr> motive_app_args;
                expr C = get_app_args(goal, motive_app_args);
                if (!motive_app_args.empty() && outer.m_inner_decl.get_intro_rule(ind_idx, ir_idx) == get_app_fn(motive_app_args.back())) {
                        m_dep_elim = true;
                        motive_app_args.pop_back();
                }
                m_motive_app = mk_app(C, motive_app_args);
            }

        expr operator()() {
            expr result = Fun(m_inner_minor_premise_args,
                              Fun(m_inner_minor_premise_rec_args,
                                  build(0, list<expr>(), list<expr>())));
            lean_trace(name({"inductive_compiler", "nested", "nested_rec"}),
                       tout() << "\n"
                       << "outer type: " << mlocal_type(m_minor_premise) << "\n"
                       << "inner val: " << result << "\n";);
            return result;
        }
    };

    expr build_nested_recursor(unsigned ind_idx, expr const & inner_recursor, expr const & outer_recursor_type) {
        expr C;
        buffer<expr> minor_premises;
        buffer<expr> indices;
        expr major_premise;
        expr goal = introduce_locals_for_nested_recursor(ind_idx, outer_recursor_type, C, minor_premises, indices, major_premise);

        // Only the minor premises need to change
        lean_assert(m_nested_decl.get_num_intro_rules(ind_idx) == minor_premises.size());
        buffer<expr> inner_minor_premises;
        for (unsigned ir_idx = 0; ir_idx < minor_premises.size(); ++ir_idx) {
            expr const & minor_premise = minor_premises[ir_idx];
            expr ty = m_tctx.relaxed_whnf(pack_type(mlocal_type(minor_premise)));

            buffer<expr> inner_minor_premise_args;
            buffer<expr> inner_minor_premise_rec_args;
            while (is_pi(ty)) {
                expr arg = mk_local_for(ty);
                if (get_app_fn(mlocal_type(arg)) != C) {
                    lean_assert(inner_minor_premise_rec_args.empty());
                    inner_minor_premise_args.push_back(arg);
                } else {
                    inner_minor_premise_rec_args.push_back(arg);
                }
                ty = m_tctx.relaxed_whnf(instantiate(binding_body(ty), arg));
            }
            inner_minor_premises.push_back(build_nested_minor_premise_fn(*this, ind_idx, ir_idx, minor_premise, inner_minor_premise_args,
                                                                         inner_minor_premise_rec_args, ty)());
        }

        return Fun(m_nested_decl.get_params(),
                   convert_locals_to_constants(
                       Fun(C,
                           Fun(minor_premises,
                               Fun(indices,
                                   Fun(major_premise,
                                       mk_app(
                                           mk_app(
                                               mk_app(
                                                   mk_app(
                                                       mk_app(inner_recursor, m_nested_decl.get_params()),
                                                       C),
                                                   inner_minor_premises),
                                               indices),
                                           major_premise)))))));
    }

    void define_nested_recursors() {
        for (unsigned ind_idx = 0; ind_idx < m_nested_decl.get_num_inds(); ++ind_idx) {
            expr const & nested_ind = m_nested_decl.get_ind(ind_idx);
            expr const & inner_ind = m_inner_decl.get_ind(ind_idx);
            declaration inner_rec = m_env.get(mlocal_name(inner_ind));

            declaration d = m_env.get(inductive::get_elim_name(mlocal_name(inner_ind)));
            level_param_names lp_names = d.get_univ_params();
            levels lvls = param_names_to_levels(lp_names);

            expr inner_recursor = mk_constant(inductive::get_elim_name(mlocal_name(inner_ind)), lvls);
            expr inner_recursor_type = m_tctx.infer(inner_recursor);

            unsigned num_params = m_nested_decl.get_num_params();
            expr inner_ty = m_tctx.relaxed_whnf(inner_recursor_type);
            for (unsigned i = 0; i < num_params; ++i) {
                inner_ty = m_tctx.relaxed_whnf(instantiate(binding_body(inner_ty), m_nested_decl.get_param(i)));
            }

            expr outer_recursor_type = Pi(m_nested_decl.get_params(), convert_locals_to_constants(unpack_type(convert_constants_to_locals(inner_ty))));
            lean_assert(!has_local(outer_recursor_type));

            expr outer_recursor_val = build_nested_recursor(ind_idx, inner_recursor, outer_recursor_type);
            lean_assert(!has_local(outer_recursor_val));

            lean_trace(name({"inductive_compiler", "nested", "nested_rec"}),
                       tout() << "[" << inductive::get_elim_name(mlocal_name(nested_ind)) << "]\n"
                       << "inner: " << inner_recursor_type << "\n"
                       << "outer: " << outer_recursor_type << "\n"
                       << "val: " << outer_recursor_val << "\n";);

            m_env = module::add(m_env, check(m_env, mk_definition(m_env, inductive::get_elim_name(mlocal_name(nested_ind)),
                                                                  lp_names, outer_recursor_type, outer_recursor_val)));
            m_tctx.set_env(m_env);
        }
    }

public:
    add_nested_inductive_decl_fn(environment const & env, options const & opts,
                                 name_map<implicit_infer_kind> const & implicit_infer_map, ginductive_decl const & nested_decl):
        m_env(env), m_opts(opts), m_implicit_infer_map(implicit_infer_map),
        m_nested_decl(nested_decl), m_inner_decl(m_nested_decl.get_lp_names(), m_nested_decl.get_params()),
        m_prefix("nest" + std::to_string(g_next_nest_id++)),
        m_tctx(env, transparency_mode::Semireducible) { }

    optional<environment> operator()() {
        if (!find_nested_occ())
            return optional<environment>();
        translate_nested_decl();
        lean_trace(name({"inductive_compiler", "nested", "inner_ind"}),
                   tout() << "adding: " << mlocal_name(m_replacement) << "\n";);

        m_env = add_inner_inductive_declaration(m_env, m_opts, m_implicit_infer_map, m_inner_decl);
        m_tctx.set_env(m_env);
        lean_assert((bool) m_env.find(mlocal_name(m_replacement)));
        compute_local_to_constant_map();

        define_nested_inds();
        define_nested_irs();
        compute_pack_info_for_nested_occ();
        define_nested_recursors();

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
    register_trace_class(name({"inductive_compiler", "nested", "nested_rec"}));
    register_trace_class(name({"inductive_compiler", "nested", "pack"}));
    register_trace_class(name({"inductive_compiler", "nested", "unpack"}));
    register_trace_class(name({"inductive_compiler", "nested", "unpack_pack"}));
    g_nested_prefix = new name(name::mk_internal_unique_name());
}

void finalize_inductive_compiler_nested() {
    delete g_nested_prefix;
}
}
