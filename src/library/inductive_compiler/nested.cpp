/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include <string>
#include <vector>
#include "kernel/inductive/inductive.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "kernel/find_fn.h"
#include "kernel/expr.h"
#include "kernel/replace_fn.h"
#include "util/sexpr/option_declarations.h"
#include "util/list_fn.h"
#include "util/fresh_name.h"
#include "library/locals.h"
#include "library/app_builder.h"
#include "library/constants.h"
#include "library/class.h"
#include "library/module.h"
#include "library/trace.h"
#include "library/type_context.h"
#include "library/inverse.h"
#include "library/attribute_manager.h"
#include "library/constructions/has_sizeof.h"
#include "library/inductive_compiler/compiler.h"
#include "library/inductive_compiler/basic.h"
#include "library/inductive_compiler/nested.h"
#include "library/inductive_compiler/util.h"
#include "library/tactic/induction_tactic.h"
#include "library/tactic/simplifier/simplifier.h"
#include "library/tactic/simplifier/simp_lemmas.h"

namespace lean {

static unsigned g_next_nest_id = 0;
static name * g_nested_prefix = nullptr;

static expr mk_local_for(expr const & b) { return mk_local(mk_fresh_name(), binding_name(b), binding_domain(b), binding_info(b)); }
static expr mk_local_for(expr const & b, name const & n) { return mk_local(mk_fresh_name(), n, binding_domain(b), binding_info(b)); }
static expr mk_local_pp(name const & n, expr const & ty) { return mk_local(mk_fresh_name(), n, ty, binder_info()); }

class add_nested_inductive_decl_fn {
    environment                   m_env;
    options                       m_opts;
    name_map<implicit_infer_kind> m_implicit_infer_map;
    ginductive_decl const &       m_nested_decl;
    ginductive_decl               m_inner_decl;
    name                          m_prefix;

    type_context                  m_tctx;

    expr                          m_nested_occ; // (fn1.{ind-ls} ind_params) without the indices

    level                         m_nested_occ_result_level;
    levels                        m_nested_occ_fn_levels;

    expr                          m_replacement; // (fn2.{nested-ls} nested_params)
    name get_replacement_name() { return const_name(get_app_fn(m_replacement)); }

    expr                          m_primitive_pack;
    expr                          m_primitive_unpack;

    buffer<buffer<buffer<bool> > > m_needs_pack; // [ind_idx][ir_idx][ir_arg_idx]

    // For the pack_ir_arg recursion
    bool                          m_in_define_nested_irs{false};
    unsigned                      m_curr_nest_idx{0};
    simp_lemmas                   m_lemmas;

    unsigned get_curr_ind_idx() { lean_assert(m_in_define_nested_irs); return m_needs_pack.size() - 1; }
    unsigned get_curr_ir_idx() { lean_assert(m_in_define_nested_irs); return m_needs_pack[get_curr_ind_idx()].size() - 1; }
    unsigned get_curr_ir_arg_idx() { lean_assert(m_in_define_nested_irs); return m_needs_pack[get_curr_ind_idx()][get_curr_ir_idx()].size(); }

    // For sizeof
    local_context                 m_synth_lctx;
    buffer<expr>                  m_param_insts;

    // For naming
    enum class fn_layer { PI, NESTED, PRIMITIVE };
    enum class fn_type { PACK, UNPACK, PACK_UNPACK, UNPACK_PACK, SIZEOF_PACK };

    struct spec_lemma {
        fn_layer     m_fn_layer;
        fn_type      m_fn_type;
        name         m_ir_name;
        buffer<expr> m_to_abstract;
        expr         m_lhs;
        expr         m_rhs;

        spec_lemma(fn_layer const & layer, fn_type const & type, name const & ir_name, buffer<expr> const & to_abstract, expr const & lhs, expr const & rhs):
            m_fn_layer(layer), m_fn_type(type), m_ir_name(ir_name), m_to_abstract(to_abstract), m_lhs(lhs), m_rhs(rhs) {}
    };

    name to_name(fn_layer l) {
        switch (l) {
        case fn_layer::PI: return "pi";
        case fn_layer::NESTED: return "nested";
        case fn_layer::PRIMITIVE: return "primitive";
        }
        lean_unreachable();
    }

    name to_name(fn_type t) {
        switch (t) {
        case fn_type::PACK: return "pack";
        case fn_type::UNPACK: return "unpack";
        case fn_type::PACK_UNPACK: return "pack_unpack";
        case fn_type::UNPACK_PACK: return "unpack_pack";
        case fn_type::SIZEOF_PACK: return "sizeof_pack";
        }
        lean_unreachable();
    }

    name rcons(name const & n, unsigned i) { return n.append_after(("_" + std::to_string(i)).c_str()); }

    name append_with_ir_arg(name const & n) { return append_with_ir_arg(n, get_curr_ir_idx(), get_curr_ir_arg_idx()); }
    name append_with_ir_arg(name const & n, unsigned ir_idx, unsigned ir_arg_idx) { return rcons(rcons(n, ir_idx), ir_arg_idx); }

    name append_with_nest_idx(name const & n) { return rcons(n, m_curr_nest_idx); }

    name mk_pi_name(fn_type t, unsigned ind_idx, unsigned ir_idx, unsigned ir_arg_idx) {
        return append_with_ir_arg(mlocal_name(m_nested_decl.get_ind(ind_idx)) + to_name(fn_layer::PI) + to_name(t), ir_idx, ir_arg_idx);
    }
    name mk_pi_name(fn_type t) { return mk_pi_name(t, get_curr_ind_idx(), get_curr_ir_idx(), get_curr_ir_arg_idx()); }
    name mk_nest_name(fn_type t) { return append_with_nest_idx(append_with_ir_arg(mlocal_name(m_nested_decl.get_ind(get_curr_ind_idx())) + to_name(fn_layer::NESTED) + to_name(t))); }
    name mk_primitive_name(fn_type t) { return m_prefix + to_name(fn_layer::PRIMITIVE) + to_name(t); }
    name mk_inner_name(name const & n) { return m_prefix + n; }
    name mk_spec_name(name const & n) { return mk_inner_name(n) + "spec"; }
    name mk_unpacked_name(name const & n) { return mk_inner_name(n) + "unpacked"; }

    // Helpers

    void add_inner_decl() {
        try {
            m_env = add_inner_inductive_declaration(m_env, m_opts, m_implicit_infer_map, m_inner_decl);
        } catch (exception & ex) {
            throw nested_exception(sstream() << "nested inductive type compiled to invalid inductive type", ex);
        }
        m_tctx.set_env(m_env);
    }

    void define_theorem(name const & n, expr const & ty, expr const & val) {
        assert_no_locals(n, ty);
        assert_no_locals(n, val);
        declaration d = mk_definition_inferring_trusted(m_env, n, to_list(m_nested_decl.get_lp_names()), ty, val, true);
        try {
            m_env = module::add(m_env, check(m_env, d));
            lean_trace(name({"inductive_compiler", "nested", "define", "success"}), tout() << n << " : " << ty << "\n";);
        } catch (exception & ex) {
            m_env = module::add(m_env, check(m_env, mk_axiom(n, to_list(m_nested_decl.get_lp_names()), ty)));
            lean_trace(name({"inductive_compiler", "nested", "define", "failure"}), tout() << n << " : " << ty << " :=\n" << val << "\n";);
        }
        m_tctx.set_env(m_env);
    }

    void define(name const & n, expr const & val) {
        // TODO(dhs): get rid of, always compute type
        define(n, m_tctx.infer(val), val);
    }

    void define(name const & n, expr const & ty, expr const & val) {
        define(n, ty, val, to_list(m_nested_decl.get_lp_names()));
    }

    void define(name const & n, expr const & ty, expr const & val, level_param_names const & lp_names) {
        assert_no_locals(n, ty);
        assert_no_locals(n, val);
        declaration d = mk_definition_inferring_trusted(m_env, n, lp_names, ty, val, true);
        try {
            m_env = module::add(m_env, check(m_env, d));
            lean_trace(name({"inductive_compiler", "nested", "define", "success"}), tout() << n << " : " << ty << " :=\n  " << val << "\n";);
        } catch (exception & ex) {
            lean_trace(name({"inductive_compiler", "nested", "define", "failure"}), tout() << n << " : " << ty << " :=\n  " << val << "\n";);
            throw nested_exception(sstream() << "error when adding '" << n << "' to the environment", ex);
        }
        m_tctx.set_env(m_env);
    }

    bool contains_non_param_locals(expr const & e) {
        if (!has_local(e))
            return false;

        bool found_non_param_local = false;
        for_each(e, [&](expr const & e, unsigned) {
                if (found_non_param_local)
                    return false;
                if (!has_local(e))
                    return false;
                if (is_local(e) && !m_nested_decl.is_param(e)) {
                    found_non_param_local = true;
                    return false;
                }
                return true;
            });
        return found_non_param_local;
    }

    void collect_non_param_locals(expr const & e, collected_locals & ls) {
       if (!has_local(e)) return;
        for_each(e, [&](expr const & e, unsigned) {
                if (!has_local(e)) return false;
                if (is_local(e) && !m_nested_decl.is_param(e)) ls.insert(e);
                return true;
            });
    }

    void collect_non_param_locals(expr const & e, collected_locals & ls, buffer<expr> const & skip) {
       if (!has_local(e)) return;
        for_each(e, [&](expr const & e, unsigned) {
                if (!has_local(e))
                    return false;
                if (is_local(e) && !m_nested_decl.is_param(e) && !std::find(skip.begin(), skip.end(), e))
                    ls.insert(e);
                return true;
            });
    }

    void initialize_synth_lctx() {
        if (optional<declaration> opt_d_has_sizeof = m_env.find(mk_has_sizeof_name(mlocal_name(m_nested_decl.get_ind(0))))) {
            local_context lctx;
            expr ty = opt_d_has_sizeof->get_type();
            for (expr const & param : m_nested_decl.get_params()) {
                ty = instantiate(binding_body(ty), param);
            }

            while (is_pi(ty) && binding_info(ty).is_inst_implicit()) {
                expr param_inst = lctx.mk_local_decl(binding_name(ty), binding_domain(ty), binding_info(ty));
                m_param_insts.push_back(param_inst);
                ty = m_tctx.whnf(instantiate(binding_body(ty), param_inst));
            }
            m_synth_lctx = lctx;
        }
    }

    ///////////////////////////////////////////
    ///// Stage 1: find nested occurrence /////
    ///////////////////////////////////////////

    bool find_nested_occ() {
        for (buffer<expr> const & irs : m_nested_decl.get_intro_rules()) {
            for (expr const & ir : irs) {
                if (find_nested_occ_in_ir_type(mlocal_type(ir)))
                    return true;
            }
        }
        return false;
    }

    bool find_nested_occ_in_ir_type(expr const & ir_type) {
        if (!m_nested_decl.has_ind_occ(ir_type))
            return false;
        expr ty = m_tctx.whnf(ir_type);
        while (is_pi(ty)) {
            expr arg_type = binding_domain(ty);
            if (find_nested_occ_in_ir_arg_type(arg_type))
                return true;
            expr l = mk_local_for(ty);
            ty = m_tctx.whnf(instantiate(binding_body(ty), l));
        }
        return false;
    }

    bool find_nested_occ_in_ir_arg_type(expr const & arg_ty) {
        if (!m_nested_decl.has_ind_occ(arg_ty))
            return false;

        expr ty = m_tctx.whnf(arg_ty);
        while (is_pi(ty)) {
            expr l = mk_local_for(ty);
            ty = m_tctx.whnf(instantiate(binding_body(ty), l));
        }

        return find_nested_occ_in_ir_arg_type_core(ty, none_expr());
    }

    bool find_nested_occ_in_ir_arg_type_core(expr const & ty, optional<expr> outer_app, unsigned num_params = 0) {
        if (!m_nested_decl.has_ind_occ(ty))
            return false;

        buffer<expr> args;
        expr fn = get_app_args(ty, args);

        if (!outer_app && m_nested_decl.is_ind(fn))
            return false;

        if (outer_app && m_nested_decl.is_ind(fn)) {
            buffer<expr> outer_params, outer_indices;
            expr outer_fn = get_app_params_indices(*outer_app, num_params, outer_params, outer_indices);

            // we found a nested occurrence
            m_nested_occ = mk_app(outer_fn, outer_params);

            // confirm that it contains no non-param locals
            if (contains_non_param_locals(m_nested_occ))
                throw exception(sstream() << "nested occurrence '" << m_nested_occ << "' contains variables that are not parameters");

            m_nested_occ_result_level = get_level(m_tctx, *outer_app);
            m_nested_occ_fn_levels = const_levels(outer_fn);

            m_replacement = m_nested_decl.mk_const_params(mk_inner_name(const_name(outer_fn)));

            lean_trace(name({"inductive_compiler", "nested", "found_occ"}),
                       tout() << m_nested_occ << "\n";);
            return true;
        }

        if (is_constant(fn) && is_ginductive(m_env, const_name(fn))) {
            unsigned num_params = get_ginductive_num_params(m_env, const_name(fn));
            for (unsigned i = 0; i < num_params; ++i) {
                if (find_nested_occ_in_ir_arg_type_core(m_tctx.whnf(args[i]), some_expr(ty), num_params))
                    return true;
            }
            throw exception("inductive type being declared cannot occur as an index of another inductive type");
        }

        throw exception("inductive type being declared can only be nested inside the parameters of other inductive types");
    }

    /////////////////////////////////////////
    ///// Stage 2: construct inner decl /////
    /////////////////////////////////////////

    expr pack_constants(expr const & e) {
        return replace(e, [&](expr const & e) {
                if (m_nested_decl.is_ind(e) || m_nested_decl.is_ir(e)) {
                    lean_assert(is_constant(e));
                    return some_expr(mk_constant(mk_inner_name(const_name(e)), const_levels(e)));
                } else {
                    return none_expr();
                }
            });
    }

    expr unpack_constants(expr const & e) {
        return replace(e, [&](expr const & e) {
                if (!is_constant(e))
                    return none_expr();
                for (unsigned ind_idx = 0; ind_idx < m_nested_decl.get_num_inds(); ++ind_idx) {
                    if (const_name(e) == mlocal_name(m_inner_decl.get_ind(ind_idx)))
                        return some_expr(mk_constant(mlocal_name(m_nested_decl.get_ind(ind_idx)), const_levels(e)));
                    for (unsigned ir_idx = 0; ir_idx < m_nested_decl.get_num_intro_rules(ind_idx); ++ir_idx) {
                        if (const_name(e) == mlocal_name(m_inner_decl.get_intro_rule(ind_idx, ir_idx)))
                            return some_expr(mk_constant(mlocal_name(m_nested_decl.get_intro_rule(ind_idx, ir_idx)), const_levels(e)));
                    }
                }
                return none_expr();
            });
    }

    expr pack_nested_occs(expr const & _e) {
        // Note: cannot use replace because we need to whnf to expose the nested occurrences
        // For the same reason, we must instantiate with locals
        // Note: only looks in the places where it would be legal to find a nested occurrence
        expr e = m_tctx.whnf(_e);
        switch (e.kind()) {
        case expr_kind::Sort:
        case expr_kind::Local:
        case expr_kind::Macro:
            return _e;
        case expr_kind::Lambda:
        case expr_kind::Pi:
        {
            expr new_dom = pack_nested_occs(binding_domain(e));
            expr l = mk_local_pp("x_new_dom", new_dom);
            expr new_body = abstract_local(pack_nested_occs(instantiate(binding_body(e), l)), l);
            return update_binding(e, new_dom, new_body);
        }
        case expr_kind::Constant:
        case expr_kind::App:
        {
            buffer<expr> args;
            expr fn = get_app_args(e, args);
            if (is_constant(fn) && is_ginductive(m_env, const_name(fn))) {
                unsigned num_params = get_ginductive_num_params(m_env, const_name(fn));
                expr candidate = mk_app(fn, num_params, args.data());
                if (candidate == m_nested_occ) {
                    return copy_tag(e, mk_app(m_replacement, args.size() - num_params, args.data() + num_params));
                } else {
                    // We track whether it was updated just so we don't whnf unnecessarily
                    // May not be necessary (or may want to do the same for bindings)
                    bool updated = false;
                    for (unsigned i = 0; i < num_params; ++i) {
                        expr new_arg = pack_nested_occs(args[i]);
                        if (new_arg != args[i]) {
                            args[i] = new_arg;
                            updated = true;
                        }
                    }
                    if (updated)
                        return copy_tag(e, mk_app(fn, args));
                    else
                        return _e;
                }
            }
            return _e;
        }
        case expr_kind::Var:
        case expr_kind::Meta:
        case expr_kind::Let:
            lean_unreachable();
        }
        lean_unreachable();
    }

    expr unpack_nested_occs(expr const & _e) {
        // Note: cannot use replace because we need to whnf to expose the nested occurrences
        // For the same reason, we must instantiate with locals
        // Note: only looks in the places where it would be legal to find a nested occurrence
        expr e = m_tctx.whnf(_e);
        switch (e.kind()) {
        case expr_kind::Sort:
        case expr_kind::Local:
        case expr_kind::Macro:
            return _e;
        case expr_kind::Lambda:
        case expr_kind::Pi:
        {
            expr new_dom = unpack_nested_occs(binding_domain(e));
            expr l = mk_local_pp("x_new_dom", new_dom);
            expr new_body = abstract_local(unpack_nested_occs(instantiate(binding_body(e), l)), l);
            return update_binding(e, new_dom, new_body);
        }
        case expr_kind::Constant:
        case expr_kind::App:
        {
            buffer<expr> args;
            expr fn = get_app_args(e, args);
            if (is_constant(fn) && is_ginductive(m_env, const_name(fn))) {
                unsigned num_params = get_ginductive_num_params(m_env, const_name(fn));
                expr candidate = mk_app(fn, num_params, args.data());
                if (candidate == m_replacement) {
                    return copy_tag(e, mk_app(m_nested_occ, args.size() - num_params, args.data() + num_params));
                } else {
                    // We track whether it was updated just so we don't whnf unnecessarily
                    // May not be necessary (or may want to do the same for bindings)
                    bool updated = false;
                    for (unsigned i = 0; i < num_params; ++i) {
                        expr new_arg = unpack_nested_occs(args[i]);
                        if (new_arg != args[i]) {
                            args[i] = new_arg;
                            updated = true;
                        }
                    }
                    if (updated)
                        return copy_tag(e, mk_app(fn, args));
                    else
                        return _e;
                }
            }
            return _e;
        }
        case expr_kind::Var:
        case expr_kind::Meta:
        case expr_kind::Let:
            lean_unreachable();
        }
        lean_unreachable();
    }

    expr pack_type(expr const & e) { return pack_constants(pack_nested_occs(e)); }
    expr unpack_type(expr const & e) { return unpack_constants(unpack_nested_occs(e)); }

    void construct_inner_decl() {
        // Construct inner inds for each of the nested inds
        for (unsigned ind_idx = 0; ind_idx < m_nested_decl.get_num_inds(); ++ind_idx) {
            expr const & ind = m_nested_decl.get_ind(ind_idx);
            expr inner_ind = mk_local(mk_inner_name(mlocal_name(ind)), mlocal_type(ind));
            m_inner_decl.get_inds().push_back(inner_ind);

            lean_trace(name({"inductive_compiler", "nested", "inner", "ind"}),
                       tout() << mlocal_name(inner_ind) << " : " << mlocal_type(inner_ind) << "\n";);

            m_inner_decl.get_intro_rules().emplace_back();
            for (expr const & ir : m_nested_decl.get_intro_rules(ind_idx)) {
                expr inner_ir = mk_local(mk_inner_name(mlocal_name(ir)), pack_type(mlocal_type(ir)));
                m_inner_decl.get_intro_rules().back().push_back(inner_ir);

            lean_trace(name({"inductive_compiler", "nested", "inner", "ir"}),
                       tout() << mlocal_name(inner_ir) << " : " << mlocal_type(inner_ir) << "\n";);
            }
        }

        // For each type mutually inductive to the nested occurrence, we mimic the type and its intro rules
        buffer<expr> nested_occ_params;
        expr nested_occ_fn = get_app_args(m_nested_occ, nested_occ_params);
        name mimic_name = const_name(nested_occ_fn);
        if (length(get_ginductive_mut_ind_names(m_env, mimic_name)) > 1)
            throw exception(sstream() << "cannot nest occurrence inside mutually inductive type '" << mimic_name << "'");

        expr c_mimic_ind = mk_app(mk_constant(mimic_name, const_levels(nested_occ_fn)), nested_occ_params);
        expr mimic_ind = mk_local(mk_inner_name(mimic_name), m_tctx.infer(c_mimic_ind));
        m_inner_decl.get_inds().push_back(mimic_ind);

        lean_trace(name({"inductive_compiler", "nested", "mimic", "ind"}),
                   tout() << mlocal_name(mimic_ind) << " : " << mlocal_type(mimic_ind) << "\n";);

        m_inner_decl.get_intro_rules().emplace_back();
        list<name> mimic_intro_rule_names = *get_ginductive_intro_rules(m_env, mimic_name);
        for (name const & ir : mimic_intro_rule_names) {
            expr c_mimic_ir = mk_app(mk_constant(ir, const_levels(nested_occ_fn)), nested_occ_params);
            expr mimic_ir = mk_local(mk_inner_name(ir), pack_type(m_tctx.infer(c_mimic_ir)));
            m_inner_decl.get_intro_rules().back().push_back(mimic_ir);
            lean_trace(name({"inductive_compiler", "nested", "mimic", "ir"}),
                       tout() << mlocal_name(mimic_ir) << " : " << mlocal_type(mimic_ir) << "\n";);
        }
    }

    ///////////////////////////////////////
    ///// Stage 3: define nested inds /////
    ///////////////////////////////////////

    void define_nested_inds() {
        for (unsigned ind_idx = 0; ind_idx < m_nested_decl.get_num_inds(); ++ind_idx) {
            expr const & ind = m_nested_decl.get_ind(ind_idx);
            expr new_ind_type = Pi(m_nested_decl.get_params(), mlocal_type(ind));
            expr new_ind_val = m_inner_decl.get_c_ind(ind_idx);

            lean_trace(name({"inductive_compiler", "nested", "nested_ind"}),
                       tout() << mlocal_name(ind) << " : " << new_ind_type << " :=\n  " << new_ind_val << "\n";);

            define(mlocal_name(ind), new_ind_type, new_ind_val);
            m_env = set_reducible(m_env, mlocal_name(ind), reducible_status::Irreducible, true);
            m_tctx.set_env(m_env);
        }
    }

    /////////////////////////////////////////////////////////////////////////////
    ///// Stage 4: sizeof-simp lemmas for inner type in terms of outer type /////
    /////////////////////////////////////////////////////////////////////////////

    void compute_inner_sizeof_simp_lemmas() {
        for (buffer<expr> const & irs : m_inner_decl.get_intro_rules()) {
            for (expr const & ir : irs) {
                // TODO(dhs): aux declarations?
                if (optional<declaration> d = m_env.find(mk_sizeof_spec_name(mlocal_name(ir)))) {
                    m_lemmas = add(m_tctx, m_lemmas, d->get_name(),
                                   unpack_constants(d->get_type()), unpack_constants(d->get_value()), LEAN_DEFAULT_PRIORITY);
                }
            }
        }
    }

    //////////////////////////////////////////////
    ///// Stage 5: define nested has_sizeofs /////
    /////////////////////////////////////////////

    void define_nested_has_sizeofs() {
        initialize_synth_lctx();
        for (unsigned ind_idx = 0; ind_idx < m_nested_decl.get_num_inds(); ++ind_idx) {
            expr const & ind = m_nested_decl.get_ind(ind_idx);
            name inner_sizeof_name = mk_has_sizeof_name(mlocal_name(m_inner_decl.get_ind(ind_idx)));
            optional<declaration> opt_d = m_env.find(inner_sizeof_name);
            if (!opt_d) return;
            define(mk_has_sizeof_name(mlocal_name(ind)), unpack_constants(opt_d->get_type()), unpack_constants(opt_d->get_value()));
            m_env = add_instance(m_env, mk_has_sizeof_name(mlocal_name(ind)), LEAN_DEFAULT_PRIORITY, true);
            m_tctx.set_env(m_env);
        }
    }

    //////////////////////////////////////
    ///// Stage 6: define nested irs /////
    //////////////////////////////////////

    void define_nested_irs() {
        flet<bool> in_define(m_in_define_nested_irs, true);
        for (unsigned ind_idx = 0; ind_idx < m_nested_decl.get_num_inds(); ++ind_idx) {
            lean_assert(m_needs_pack.size() == ind_idx);
            m_needs_pack.emplace_back();
            for (unsigned ir_idx = 0; ir_idx < m_nested_decl.get_num_intro_rules(ind_idx); ++ir_idx) {
                lean_assert(m_needs_pack[ind_idx].size() == ir_idx);
                m_needs_pack[ind_idx].emplace_back();
                expr const & ir = m_nested_decl.get_intro_rule(ind_idx, ir_idx);

                buffer<expr> locals;
                buffer<expr> result_args;

                expr ty = m_tctx.whnf(mlocal_type(ir));
                while (is_pi(ty)) {
                    expr l = mk_local_for(ty);
                    if (auto packed_arg = pack_ir_arg(l)) {
                        m_needs_pack[ind_idx][ir_idx].push_back(true);
                        result_args.push_back(*packed_arg);
                    } else {
                        m_needs_pack[ind_idx][ir_idx].push_back(false);
                        result_args.push_back(l);
                    }
                    locals.push_back(l);
                    ty = m_tctx.whnf(instantiate(binding_body(ty), l));
                }

                expr new_ir_val  = Fun(m_nested_decl.get_params(), Fun(locals, mk_app(m_inner_decl.get_c_ir_params(ind_idx, ir_idx), result_args)));
                expr new_ir_type = Pi(m_nested_decl.get_params(), mlocal_type(ir));
                implicit_infer_kind k = get_implicit_infer_kind(m_implicit_infer_map, mlocal_name(ir));
                new_ir_type = infer_implicit_params(new_ir_type, m_nested_decl.get_params().size(), k);

                define(mlocal_name(ir), new_ir_type, new_ir_val);
                m_env = set_reducible(m_env, mlocal_name(ir), reducible_status::Irreducible, true);
                m_tctx.set_env(m_env);
            }
        }
    }

    optional<expr> pack_ir_arg(expr const & ir_arg) {
        if (auto pack_fn = build_pi_pack_unpack(mlocal_type(ir_arg))) {
            return some_expr(mk_app(*pack_fn, ir_arg));
        } else {
            return none_expr();
        }
    }

    optional<expr> build_pi_pack_unpack(expr const & arg_ty) {
        expr ty = m_tctx.whnf(arg_ty);
        if (ty == pack_type(ty))
            return optional<expr>();

        expr x_to_pack = mk_local_pp("x_to_pack", ty);
        expr x_to_unpack = mk_local_pp("x_to_unpack", pack_type(ty));

        buffer<expr> pi_args;
        while (is_pi(ty)) {
            expr l = mk_local_for(ty);
            pi_args.push_back(l);
            ty = m_tctx.whnf(instantiate(binding_body(ty), l));
        }
        expr body_to_pack = mk_app(x_to_pack, pi_args);
        expr body_to_unpack = mk_app(x_to_unpack, pi_args);

        lean_assert(m_tctx.is_def_eq(m_tctx.infer(body_to_pack), ty));
        lean_assert(m_tctx.is_def_eq(m_tctx.infer(body_to_unpack), pack_type(ty)));

        if (ty == pack_type(ty))
            return none_expr();

        buffer<expr> args;
        expr fn = get_app_args(ty, args);

        if (!is_constant(fn) || !is_ginductive(m_env, const_name(fn)))
            return none_expr();

        unsigned num_params = get_ginductive_num_params(m_env, const_name(fn));

        buffer<expr> params, indices;
        split_params_indices(args, num_params, params, indices);
        optional<expr_pair> nested_pack_unpack = build_nested_pack_unpack(fn, params);
        if (!nested_pack_unpack)
            return none_expr();

        expr const & nested_pack_fn = nested_pack_unpack->first;
        expr const & nested_unpack_fn = nested_pack_unpack->second;

        expr pre_pi_pack = Fun(x_to_pack, Fun(pi_args, mk_app(mk_app(nested_pack_fn, indices), body_to_pack)));
        expr pre_pi_unpack = Fun(x_to_unpack, Fun(pi_args, mk_app(mk_app(nested_unpack_fn, indices), body_to_unpack)));

        collected_locals ls;
        collect_non_param_locals(pre_pi_pack, ls);
        buffer<expr> const & ldeps = ls.get_collected();

        define(mk_pi_name(fn_type::PACK), Fun(m_nested_decl.get_params(), Fun(ldeps, pre_pi_pack)));
        define(mk_pi_name(fn_type::UNPACK), Fun(m_nested_decl.get_params(), Fun(ldeps, pre_pi_unpack)));

        expr pi_pack = mk_app(m_nested_decl.mk_const_params(mk_pi_name(fn_type::PACK)), ldeps);
        expr pi_unpack = mk_app(m_nested_decl.mk_const_params(mk_pi_name(fn_type::UNPACK)), ldeps);

        prove_pi_pack_unpack(pi_pack, pi_unpack, ldeps, nested_pack_fn, nested_unpack_fn, arg_ty);
        prove_pi_unpack_pack(pi_pack, pi_unpack, ldeps, nested_pack_fn, nested_unpack_fn, arg_ty);
        prove_pi_sizeof_pack(pi_pack, ldeps, nested_pack_fn, arg_ty);

        return some_expr(pi_pack);
    }

    optional<expr_pair> build_nested_pack_unpack(expr const & fn, buffer<expr> const & params) {
        if (mk_app(fn, params) == m_nested_occ)
            return optional<expr_pair>(m_primitive_pack, m_primitive_unpack);

        // TODO(dhs): handle nested
        throw exception(sstream() << "nested occurrence '" << m_nested_occ << "' is doubly-nested, only singly-nested currently supported");
        return optional<expr_pair>();
    }

    void build_primitive_pack_unpack() {
        m_primitive_pack = m_nested_decl.mk_const_params(mk_primitive_name(fn_type::PACK));
        m_primitive_unpack = m_nested_decl.mk_const_params(mk_primitive_name(fn_type::UNPACK));

        buffer<expr> nest_params;
        expr nest_fn = get_app_args(m_nested_occ, nest_params);

        expr remaining_unpacked_type = m_tctx.whnf(m_tctx.infer(m_nested_occ));
        expr remaining_packed_type = m_tctx.whnf(m_tctx.infer(m_replacement));
        lean_assert(remaining_unpacked_type == remaining_packed_type);
        expr remaining_type = remaining_unpacked_type;

        // 1. elim levels
        list<level> pack_elim_levels, unpack_elim_levels;
        {
            pack_elim_levels = const_levels(nest_fn);
            declaration d_nest = m_env.get(inductive::get_elim_name(const_name(nest_fn)));
            if (length(pack_elim_levels) < d_nest.get_num_univ_params()) {
                lean_assert(length(pack_elim_levels) + 1 == d_nest.get_num_univ_params());
                pack_elim_levels = list<level>(sort_level(get_ind_result_type(m_tctx, m_replacement)), pack_elim_levels);
            }
            unpack_elim_levels = m_inner_decl.get_levels();
            declaration d_inner = m_env.get(inductive::get_elim_name(get_replacement_name()));
            if (length(unpack_elim_levels) < d_inner.get_num_univ_params()) {
                lean_assert(length(unpack_elim_levels) + 1 == d_inner.get_num_univ_params());
                unpack_elim_levels = list<level>(m_nested_occ_result_level, unpack_elim_levels);
            }
        }

        // 2. motives
        auto construct_C = [&](expr const & start, expr const & end) {
            expr C = end;
            expr ty = remaining_type;

            buffer<expr> locals;
            while (is_pi(ty)) {
                expr l = mk_local_for(ty);
                locals.push_back(l);
                C = mk_app(C, l);
                ty = m_tctx.whnf(instantiate(binding_body(ty), l));
            }
            expr ignore = mk_local_pp("x_ignore", mk_app(start, locals));
            locals.push_back(ignore);
            return Fun(locals, C);
        };

        expr pack_C = construct_C(m_nested_occ, m_replacement);
        expr unpack_C = construct_C(m_replacement, m_nested_occ);

        lean_trace(name({"inductive_compiler", "nested", "pack", "primitive"}), tout() << " C := " << pack_C << "\n";);
        lean_trace(name({"inductive_compiler", "nested", "unpack", "primitive"}), tout() << " C := " << unpack_C << "\n";);

        // 3. minor premises
        list<name> intro_rules = *get_ginductive_intro_rules(m_env, const_name(nest_fn));
        buffer<expr> pack_minor_premises, unpack_minor_premises;
        buffer<spec_lemma> spec_lemmas;
        for (name const & intro_rule : intro_rules) {
            expr c_unpacked_ir = mk_app(mk_constant(intro_rule, const_levels(nest_fn)), nest_params);
            expr c_packed_ir = m_inner_decl.mk_const_params(mk_inner_name(intro_rule));

            expr unpacked_ir_type = m_tctx.whnf(m_tctx.infer(c_unpacked_ir));
            expr packed_ir_type = m_tctx.whnf(m_tctx.infer(c_packed_ir));

            // for definition
            buffer<expr> unpacked_rec_args;
            buffer<expr> unpacked_locals;
            buffer<expr> unpacked_return_args;

            buffer<expr> packed_locals;
            buffer<expr> packed_rec_args;
            buffer<expr> packed_return_args;

            // for lemmas
            buffer<expr> unpacked_lhs_args;
            buffer<expr> unpacked_rhs_args;

            buffer<expr> packed_lhs_args;
            buffer<expr> packed_rhs_args;

            while (is_pi(unpacked_ir_type) && is_pi(packed_ir_type)) {
                buffer<expr> unpacked_arg_args;
                expr unpacked_arg_fn = get_app_args(binding_domain(unpacked_ir_type), unpacked_arg_args);

                buffer<expr> packed_arg_args;
                expr packed_arg_fn = get_app_args(binding_domain(packed_ir_type), packed_arg_args);

                expr unpacked_l = mk_local_for(unpacked_ir_type);
                unpacked_locals.push_back(unpacked_l);
                unpacked_lhs_args.push_back(unpacked_l);

                expr packed_l = mk_local_for(packed_ir_type);
                packed_locals.push_back(packed_l);
                packed_lhs_args.push_back(packed_l);

                if (unpacked_arg_fn == nest_fn) {
                    // it is a recursive argument
                    expr unpacked_rec_arg_type = mk_app(m_replacement, unpacked_arg_args.size() - nest_params.size(), unpacked_arg_args.data() + nest_params.size());
                    expr unpacked_l_rec = mk_local_pp("x_unpacked", unpacked_rec_arg_type);
                    unpacked_rec_args.push_back(unpacked_l_rec);
                    unpacked_return_args.push_back(unpacked_l_rec);
                    unpacked_rhs_args.push_back(mk_app(mk_app(m_primitive_pack, unpacked_arg_args.size() - nest_params.size(), unpacked_arg_args.data() + nest_params.size()),
                                                       unpacked_l));

                    expr packed_rec_arg_type = mk_app(m_nested_occ, packed_arg_args.size() - m_nested_decl.get_num_params(), packed_arg_args.data() + m_nested_decl.get_num_params());
                    expr packed_l_rec = mk_local_pp("x_packed", packed_rec_arg_type);
                    packed_rec_args.push_back(packed_l_rec);
                    packed_return_args.push_back(packed_l_rec);
                    packed_rhs_args.push_back(mk_app(mk_app(m_primitive_unpack, packed_arg_args.size() - m_nested_decl.get_num_params(), packed_arg_args.data() + m_nested_decl.get_num_params()),
                                                     packed_l));
                } else {
                    assert_def_eq(m_env, mlocal_type(unpacked_l), mlocal_type(packed_l));
                    if (mlocal_type(unpacked_l) != mlocal_type(packed_l)) {
                        // We want to replace [nest.foo] with [foo] so that the two are structurally equal
                        // Issue: other the type-context will not be able to unify them without transparency_mode::All
                        packed_l = unpacked_l;
                        packed_locals.back() = unpacked_l;
                        packed_lhs_args.back() = unpacked_l;
                    }
                    unpacked_return_args.push_back(unpacked_l);
                    unpacked_rhs_args.push_back(unpacked_l);

                    packed_return_args.push_back(packed_l);
                    packed_rhs_args.push_back(packed_l);
                }
                unpacked_ir_type = m_tctx.whnf(instantiate(binding_body(unpacked_ir_type), unpacked_l));
                packed_ir_type = m_tctx.whnf(instantiate(binding_body(packed_ir_type), packed_l));
            }

            unpacked_locals.append(unpacked_rec_args);
            packed_locals.append(packed_rec_args);

            expr unpacked_minor_premise = Fun(unpacked_locals, mk_app(c_packed_ir, unpacked_return_args));
            expr packed_minor_premise = Fun(packed_locals, mk_app(c_unpacked_ir, packed_return_args));
            pack_minor_premises.push_back(unpacked_minor_premise);
            unpack_minor_premises.push_back(packed_minor_premise);

            lean_trace(name({"inductive_compiler", "nested", "pack", "primitive"}), tout() << " mp := " << unpacked_minor_premise << "\n";);
            lean_trace(name({"inductive_compiler", "nested", "unpack", "primitive"}), tout() << " mp := " << packed_minor_premise << "\n";);

            buffer<expr> unpacked_ir_result_indices, packed_ir_result_indices;
            get_app_indices(unpacked_ir_type, nest_params.size(), unpacked_ir_result_indices);
            get_app_indices(packed_ir_type, m_nested_decl.get_num_params(), packed_ir_result_indices);

            expr unpacked_lhs = mk_app(mk_app(m_primitive_pack, unpacked_ir_result_indices), mk_app(c_unpacked_ir, unpacked_lhs_args));
            expr unpacked_rhs = mk_app(c_packed_ir, unpacked_rhs_args);
            spec_lemmas.push_back(spec_lemma(fn_layer::PRIMITIVE, fn_type::PACK, intro_rule, unpacked_lhs_args, unpacked_lhs, unpacked_rhs));

            expr packed_lhs = mk_app(mk_app(m_primitive_unpack, packed_ir_result_indices), mk_app(c_packed_ir, packed_lhs_args));
            expr packed_rhs = mk_app(c_unpacked_ir, packed_rhs_args);
            spec_lemmas.push_back(spec_lemma(fn_layer::PRIMITIVE, fn_type::UNPACK, mk_inner_name(intro_rule), packed_lhs_args, packed_lhs, packed_rhs));

            lean_trace(name({"inductive_compiler", "nested", "pack", "primitive"}), tout() << " lemma : " << unpacked_lhs << " = " << unpacked_rhs << "\n";);
            lean_trace(name({"inductive_compiler", "nested", "unpack", "primitive"}), tout() << " lemma : " << packed_lhs << " = " << packed_rhs << "\n";);
        }

        // Indices
        buffer<expr> indices;
        {
            expr ty = m_tctx.whnf(remaining_type);
            while (is_pi(ty)) {
                expr l = mk_local_for(ty);
                indices.push_back(l);
                ty = m_tctx.whnf(instantiate(binding_body(ty), l));
            }
        }

        expr primitive_pack_ty = Pi(m_nested_decl.get_params(), Pi(indices, mk_arrow(mk_app(m_nested_occ, indices), mk_app(m_replacement, indices))));
        expr primitive_pack_val = Fun(m_nested_decl.get_params(),
                                      mk_app(mk_app(mk_app(mk_constant(inductive::get_elim_name(const_name(nest_fn)), pack_elim_levels),
                                                           nest_params), pack_C), pack_minor_premises));

        expr primitive_unpack_ty = Pi(m_nested_decl.get_params(), Pi(indices, mk_arrow(mk_app(m_replacement, indices), mk_app(m_nested_occ, indices))));
        expr primitive_unpack_val = Fun(m_nested_decl.get_params(),
                                        mk_app(mk_app(mk_app(mk_constant(inductive::get_elim_name(get_replacement_name()), unpack_elim_levels),
                                                             m_nested_decl.get_params()), unpack_C), unpack_minor_premises));

        define(mk_primitive_name(fn_type::PACK), primitive_pack_ty, primitive_pack_val);
        define(mk_primitive_name(fn_type::UNPACK), primitive_unpack_ty, primitive_unpack_val);

        for (auto const & slemma : spec_lemmas) {
            name n  = mk_spec_name(to_name(slemma.m_fn_layer) + to_name(slemma.m_fn_type) + slemma.m_ir_name);
            expr ty = Pi(m_nested_decl.get_params(), Pi(slemma.m_to_abstract, mk_eq(m_tctx, slemma.m_lhs, slemma.m_rhs)));
            expr pf = Fun(m_nested_decl.get_params(), Fun(slemma.m_to_abstract, force_recursors(slemma.m_lhs)));
            define_theorem(n, ty, pf);
            m_lemmas = add_poly(m_tctx, m_lemmas, n, LEAN_DEFAULT_PRIORITY);
        }

        prove_primitive_pack_unpack(indices);
        prove_primitive_unpack_pack(indices);
        prove_primitive_pack_sizeof(indices);
    }

    /////////////////////////////
    ///// Stage 5b: proofs //////
    /////////////////////////////

    expr force_recursors(expr const & lhs) {
        // TODO(dhs): handle stuck recursors
        // Returns a proof of type [lhs = rhs]
        return mk_eq_refl(m_tctx, lhs);
    }

    expr prove_by_simp(local_context const & lctx, expr const & thm, list<expr> Hs, simp_lemmas const & lemmas) {
        simp_lemmas all_lemmas = lemmas;
        // TODO(dhs): we need to override the [simp] options
        // TODO(dhs): irreducible is not ideal, but we need to be able to unify [foo] with [nest.foo]
        type_context tctx(m_env, m_tctx.get_options(), lctx);
        for (expr const & H : Hs) {
            expr H_type = tctx.infer(H);
            all_lemmas = add(tctx, all_lemmas, mlocal_name(H), H_type, H, LEAN_DEFAULT_PRIORITY);
        }
        simp_result r = simplify(tctx, get_eq_name(), all_lemmas, thm);
        lean_assert(r.get_new() == mk_true());
        return mk_app(tctx, get_eq_mpr_name(), r.get_proof(), mk_true_intro());
    }

    expr prove_by_induction_simp(name const & rec_name, expr const & thm, simp_lemmas const & lemmas) {
        expr ty = thm;
        metavar_context mctx;

        // Note: type_context only used to manage locals and abstract at the end
        type_context tctx(m_env, m_tctx.get_options());
        type_context::tmp_locals locals(tctx);

        while (is_pi(ty)) {
            expr l = locals.push_local_from_binding(ty);
            ty = instantiate(binding_body(ty), l);
        }
        expr H = locals.as_buffer().back();
        expr goal = mctx.mk_metavar_decl(tctx.lctx(), ty);
        list<list<expr> > subgoal_hypotheses;
        hsubstitution_list subgoal_substitutions;
        list<name> ns;
        list<expr> subgoals = induction(tctx.env(), tctx.get_options(), transparency_mode::Reducible, mctx,
                                        goal, H, rec_name, ns, &subgoal_hypotheses, &subgoal_substitutions);

        for_each2(subgoals, subgoal_hypotheses, [&](expr const & m, list<expr> const & Hs) {
                metavar_decl d = *mctx.get_metavar_decl(m);
                expr pf = prove_by_simp(d.get_context(), d.get_type(), Hs, lemmas);
                mctx.assign(m, pf);
            });

        expr pf = mctx.instantiate_mvars(goal);
        lean_assert(!has_expr_metavar(pf));
        return locals.mk_lambda(pf);
    }

    void prove_primitive_pack_unpack(buffer<expr> const & index_locals) {
        // TODO(dhs): better check for dep-elim
        name n = mk_primitive_name(fn_type::PACK_UNPACK);
        expr x_packed = mk_local_pp("x_packed", mk_app(m_replacement, index_locals));
        expr lhs = mk_app(mk_app(m_primitive_pack, index_locals), mk_app(mk_app(m_primitive_unpack, index_locals), x_packed));
        expr goal = mk_eq(m_tctx, lhs, x_packed);
        expr primitive_pack_unpack_type = Pi(m_nested_decl.get_params(), Pi(index_locals, Pi(x_packed, goal)));
        expr primitive_pack_unpack_val;
        if (m_tctx.is_prop(mlocal_type(x_packed))) {
            primitive_pack_unpack_val = Fun(m_nested_decl.get_params(), Fun(index_locals, Fun(x_packed, mk_eq_refl(m_tctx, x_packed))));
        } else {
            // We need to create a special recursor for the packed type, to replace [nest.foo] with [foo]
            declaration d_rec = m_env.get(inductive::get_elim_name(mlocal_name(m_inner_decl.get_inds().back())));
            name lifted_rec_name = mk_unpacked_name(d_rec.get_name());
            define(lifted_rec_name, unpack_constants(d_rec.get_type()), unpack_constants(d_rec.get_value()), d_rec.get_univ_params());
            primitive_pack_unpack_val = prove_by_induction_simp(lifted_rec_name, primitive_pack_unpack_type, m_lemmas);
        }
        define_theorem(n, primitive_pack_unpack_type, primitive_pack_unpack_val);
        m_lemmas = add_poly(m_tctx, m_lemmas, n, LEAN_DEFAULT_PRIORITY);
    }

    void prove_primitive_unpack_pack(buffer<expr> const & index_locals) {
        // TODO(dhs): better check for dep-elim
        name n = mk_primitive_name(fn_type::UNPACK_PACK);
        expr x_unpacked = mk_local_pp("x_unpacked", mk_app(m_nested_occ, index_locals));
        name rec_name = inductive::get_elim_name(const_name(get_app_fn(m_nested_occ)));
        expr lhs = mk_app(mk_app(m_primitive_unpack, index_locals), mk_app(mk_app(m_primitive_pack, index_locals), x_unpacked));
        expr goal = mk_eq(m_tctx, lhs, x_unpacked);
        expr primitive_unpack_pack_type = Pi(m_nested_decl.get_params(), Pi(index_locals, Pi(x_unpacked, goal)));
        expr primitive_unpack_pack_val;
        if (m_tctx.is_prop(mlocal_type(x_unpacked))) {
            primitive_unpack_pack_val = Fun(m_nested_decl.get_params(), Fun(index_locals, Fun(x_unpacked, mk_eq_refl(m_tctx, x_unpacked))));
        } else {
            primitive_unpack_pack_val = prove_by_induction_simp(rec_name, primitive_unpack_pack_type, m_lemmas);
        }
        define_theorem(n, primitive_unpack_pack_type, primitive_unpack_pack_val);
        m_lemmas = add_poly(m_tctx, m_lemmas, n, LEAN_DEFAULT_PRIORITY);
    }

    void prove_primitive_pack_sizeof(buffer<expr> const & index_locals) {
        // TODO(dhs): better check for dep-elim
        name n = mk_primitive_name(fn_type::SIZEOF_PACK);
        type_context tctx_synth(m_env, m_tctx.get_options(), m_synth_lctx);

        expr x_unpacked = mk_local_pp("x_unpacked", mk_app(m_nested_occ, index_locals));
        expr lhs = mk_app(m_tctx, get_sizeof_name(), mk_app(mk_app(m_primitive_pack, index_locals), x_unpacked));
        expr rhs = mk_app(m_tctx, get_sizeof_name(), x_unpacked);
        expr goal = mk_eq(m_tctx, lhs, rhs);
        expr primitive_sizeof_pack_type = Pi(m_nested_decl.get_params(), tctx_synth.mk_pi(m_param_insts, Pi(index_locals, Pi(x_unpacked, goal))));
        expr primitive_sizeof_pack_val;
        if (m_tctx.is_prop(mlocal_type(x_unpacked))) {
            primitive_sizeof_pack_val = Fun(m_nested_decl.get_params(), tctx_synth.mk_lambda(m_param_insts, Fun(index_locals, Fun(x_unpacked, mk_eq_refl(m_tctx, mk_nat_zero())))));
        } else {
            name rec_name = inductive::get_elim_name(const_name(get_app_fn(m_nested_occ)));
            simp_lemmas lemmas = join(m_lemmas, get_sizeof_simp_lemmas(m_tctx));
            primitive_sizeof_pack_val = prove_by_induction_simp(rec_name, primitive_sizeof_pack_type, lemmas);
        }
        define_theorem(n, primitive_sizeof_pack_type, primitive_sizeof_pack_val);
        m_lemmas = add_poly(m_tctx, m_lemmas, n, LEAN_DEFAULT_PRIORITY);
    }

    expr prove_by_funext(expr const & goal, expr const & fn1, expr const & fn2) {
        buffer<expr> args;
        expr fn = get_app_args(goal, args);
        lean_assert(is_constant(fn) && const_name(fn) == get_eq_name());
        buffer<expr> pi_args;

        type_context tctx(m_env, m_tctx.get_options());

        expr ty = tctx.whnf(args[0]);
        while (is_pi(ty)) {
            expr l = tctx.push_local(binding_name(ty), binding_domain(ty), binding_info(ty));
            pi_args.push_back(l);
            ty = tctx.whnf(instantiate(binding_body(ty), l));
        }

        buffer<expr> result_args, result_params, result_indices;
        expr result_fn = get_app_args(ty, result_args);
        split_params_indices(result_args, get_ginductive_num_params(m_env, const_name(result_fn)), result_params, result_indices);
        expr lhs = mk_app(mk_app(fn1, result_indices), mk_app(mk_app(fn2, result_indices), mk_app(args[2], pi_args)));
        expr rhs = mk_app(args[2], pi_args);
        expr pi_goal = mk_eq(tctx, lhs, rhs);
        expr pi_pf = prove_by_simp(tctx.lctx(), pi_goal, list<expr>(), m_lemmas);

        for (unsigned pi_arg_idx = pi_args.size(); pi_arg_idx > 0; pi_arg_idx--) {
            pi_pf = mk_funext(tctx, tctx.mk_lambda(pi_args[pi_arg_idx-1], pi_pf));
        }

        return pi_pf;
    }

    void prove_pi_pack_unpack(expr const & pi_pack, expr const & pi_unpack, buffer<expr> const & ldeps, expr const & nested_pack_fn, expr const & nested_unpack_fn, expr const & arg_ty) {
        name n = mk_pi_name(fn_type::PACK_UNPACK);
        expr x_packed = mk_local_pp("x_packed", pack_type(arg_ty));
        expr lhs = mk_app(pi_pack, mk_app(pi_unpack, x_packed));
        expr goal = mk_eq(m_tctx, lhs, x_packed);
        expr pi_pack_unpack_type = Pi(m_nested_decl.get_params(), Pi(ldeps, Pi(x_packed, goal)));
        expr pi_pack_unpack_val = Fun(m_nested_decl.get_params(), Fun(ldeps, Fun(x_packed, prove_by_funext(goal, nested_pack_fn, nested_unpack_fn))));
        define_theorem(n, pi_pack_unpack_type, pi_pack_unpack_val);
        m_env = add_inverse_lemma(m_env, n, true);
        m_tctx.set_env(m_env);
    }

    void prove_pi_unpack_pack(expr const & pi_pack, expr const & pi_unpack, buffer<expr> const & ldeps, expr const & nested_pack_fn, expr const & nested_unpack_fn, expr const & arg_ty) {
        name n = mk_pi_name(fn_type::UNPACK_PACK);
        expr x_unpacked = mk_local_pp("x_unpacked", arg_ty);
        expr lhs = mk_app(pi_unpack, mk_app(pi_pack, x_unpacked));
        expr goal = mk_eq(m_tctx, lhs, x_unpacked);
        expr pi_unpack_pack_type = Pi(m_nested_decl.get_params(), Pi(ldeps, Pi(x_unpacked, goal)));
        expr pi_unpack_pack_val = Fun(m_nested_decl.get_params(), Fun(ldeps, Fun(x_unpacked, prove_by_funext(goal, nested_unpack_fn, nested_pack_fn))));
        define_theorem(n, pi_unpack_pack_type, pi_unpack_pack_val);
        m_env = add_inverse_lemma(m_env, n, true);
        m_tctx.set_env(m_env);
    }

    void prove_pi_sizeof_pack(expr const & pi_pack, buffer<expr> const & ldeps, expr const & nested_pack_fn, expr const & arg_ty) {
        name n = mk_pi_name(fn_type::SIZEOF_PACK);
        type_context tctx_synth(m_env, m_tctx.get_options(), m_synth_lctx);

        expr x_unpacked = mk_local_pp("x_unpacked", arg_ty);
        expr lhs = mk_app(m_tctx, get_sizeof_name(), mk_app(pi_pack, x_unpacked));
        expr rhs = mk_app(m_tctx, get_sizeof_name(), x_unpacked);
        expr goal = mk_eq(m_tctx, lhs, rhs);
        expr pi_unpack_pack_type = Pi(m_nested_decl.get_params(), Pi(ldeps, Pi(x_unpacked, goal)));
        expr pi_unpack_pack_val;

        expr ty = tctx_synth.whnf(arg_ty);
        if (is_pi(ty)) {
            pi_unpack_pack_val = Fun(m_nested_decl.get_params(), Fun(ldeps, Fun(x_unpacked, mk_eq_refl(tctx_synth, mk_nat_zero()))));
        } else {
            buffer<expr> result_args, result_params, result_indices;
            expr result_fn = get_app_args(ty, result_args);
            split_params_indices(result_args, get_ginductive_num_params(m_env, const_name(result_fn)), result_params, result_indices);
            expr lhs = mk_app(m_tctx, get_sizeof_name(), mk_app(mk_app(nested_pack_fn, result_indices), x_unpacked));
            expr rhs = mk_app(m_tctx, get_sizeof_name(), x_unpacked);
            expr pi_pf = prove_by_simp(tctx_synth.lctx(), mk_eq(tctx_synth, lhs, rhs), list<expr>(), m_lemmas);
            pi_unpack_pack_val = Fun(m_nested_decl.get_params(), Fun(ldeps, Fun(x_unpacked, pi_pf)));
        }
        define_theorem(n, pi_unpack_pack_type, pi_unpack_pack_val);
        m_env = set_simp_sizeof(m_env, n);
        m_tctx.set_env(m_env);
    }

    ////////////////////////////////////////////
    ///// Stage 7: define nested recursors /////
    ////////////////////////////////////////////

    void define_nested_recursors() {
        for (unsigned ind_idx = 0; ind_idx < m_nested_decl.get_num_inds(); ++ind_idx) {
            expr const & nested_ind = m_nested_decl.get_ind(ind_idx);
            expr const & inner_ind = m_inner_decl.get_ind(ind_idx);

            declaration d = m_env.get(inductive::get_elim_name(mlocal_name(inner_ind)));
            level_param_names lp_names = d.get_univ_params();
            levels lvls = param_names_to_levels(lp_names);

            expr inner_recursor = mk_app(mk_constant(inductive::get_elim_name(mlocal_name(inner_ind)), lvls), m_nested_decl.get_params());
            expr inner_recursor_type = m_tctx.infer(inner_recursor);

            expr outer_recursor_type = Pi(m_nested_decl.get_params(), unpack_type(inner_recursor_type));
            expr outer_recursor_val = Fun(m_nested_decl.get_params(), build_nested_recursor(ind_idx, inner_recursor, unpack_type(inner_recursor_type)));
            define(inductive::get_elim_name(mlocal_name(nested_ind)), outer_recursor_type, outer_recursor_val, lp_names);
        }
    }

    expr introduce_locals_for_nested_recursor(unsigned ind_idx, expr const & outer_recursor_type,
                                              expr & C, buffer<expr> & minor_premises,
                                              buffer<expr> & indices, expr & major_premise) {
        expr ty = m_tctx.whnf(outer_recursor_type);

        C = mk_local_for(ty, "C");
        ty = m_tctx.whnf(instantiate(binding_body(ty), C));

        for (unsigned ir_idx = 0; ir_idx < m_nested_decl.get_num_intro_rules(ind_idx); ++ir_idx) {
            expr minor_premise = mk_local_for(ty);
            minor_premises.push_back(minor_premise);
            ty = m_tctx.whnf(instantiate(binding_body(ty), minor_premise));
        }

        while (is_pi(ty)) {
            expr l = mk_local_for(ty);
            ty = m_tctx.whnf(instantiate(binding_body(ty), l));
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

        expr m_motive_app;

        expr build(unsigned arg_idx, list<expr> rev_ir_args, list<expr> rev_mp_args) {
            // TODO(dhs): need the arity so that the app-builder has a chance
            if (arg_idx == m_inner_minor_premise_args.size()) {
                buffer<expr> mp_args;
                to_buffer(reverse(rev_mp_args), mp_args);
                return mk_app(mk_app(m_minor_premise, mp_args), m_inner_minor_premise_rec_args);
            }

            expr const & arg = m_inner_minor_premise_args[arg_idx];

            bool needs_pack = m_outer.m_needs_pack[m_ind_idx][m_ir_idx][arg_idx];
            if (!needs_pack)
                return build(arg_idx+1, list<expr>(arg, rev_ir_args), list<expr>(arg, rev_mp_args));

            buffer<expr> ir_args;
            to_buffer(reverse(rev_ir_args), ir_args);

            buffer<expr> mp_args;
            to_buffer(reverse(rev_mp_args), mp_args);

            // Need to store the number-of-ldeps so that I can pass the right mask to the app-builder
            name pack_fn = m_outer.mk_pi_name(fn_type::PACK, m_ind_idx, m_ir_idx, arg_idx);
            name unpack_fn = m_outer.mk_pi_name(fn_type::UNPACK, m_ind_idx, m_ir_idx, arg_idx);
            name pack_unpack_fn = m_outer.mk_pi_name(fn_type::PACK_UNPACK, m_ind_idx, m_ir_idx, arg_idx);

            expr motive = Fun(m_inner_minor_premise_args[arg_idx],
                              mk_app(m_motive_app,
                                     mk_app(
                                         mk_app(m_outer.m_inner_decl.get_c_ir_params(m_ind_idx, m_ir_idx),
                                                ir_args),
                                         m_inner_minor_premise_args.size() - arg_idx,
                                         m_inner_minor_premise_args.data() + arg_idx)));

            expr rest = build(arg_idx+1,
                              list<expr>(mk_app(m_outer.m_tctx, pack_fn, mk_app(m_outer.m_tctx, unpack_fn, arg)), rev_ir_args),
                              list<expr>(mk_app(m_outer.m_tctx, unpack_fn, arg), rev_mp_args));
            expr equality_proof = mk_app(m_outer.m_tctx, pack_unpack_fn, arg);

            assert_type_correct(m_outer.m_env, motive);
            assert_type_correct(m_outer.m_env, rest);
            assert_type_correct(m_outer.m_env, equality_proof);

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
                // TODO(dhs): remove once assert passes
                buffer<expr> motive_app_args;
                expr C = get_app_args(goal, motive_app_args);
                lean_assert(!motive_app_args.empty() && outer.m_inner_decl.get_c_ir(ind_idx, ir_idx) == get_app_fn(motive_app_args.back()));
                m_motive_app = app_fn(goal);
            }

        expr operator()() {
            return Fun(m_inner_minor_premise_args,
                       Fun(m_inner_minor_premise_rec_args,
                           build(0, list<expr>(), list<expr>())));
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
            expr ty = m_tctx.whnf(pack_type(mlocal_type(minor_premise)));

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
                ty = m_tctx.whnf(instantiate(binding_body(ty), arg));
            }
            inner_minor_premises.push_back(build_nested_minor_premise_fn(*this, ind_idx, ir_idx, minor_premise, inner_minor_premise_args,
                                                                         inner_minor_premise_rec_args, ty)());
        }

        return Fun(C,
                   Fun(minor_premises,
                       Fun(indices,
                           Fun(major_premise,
                               mk_app(mk_app(mk_app(mk_app(inner_recursor, C), inner_minor_premises), indices), major_premise)))));
    }


public:
    add_nested_inductive_decl_fn(environment const & env, options const & opts,
                                 name_map<implicit_infer_kind> const & implicit_infer_map, ginductive_decl const & nested_decl):
        m_env(env), m_opts(opts), m_implicit_infer_map(implicit_infer_map),
        m_nested_decl(nested_decl), m_inner_decl(m_nested_decl.get_lp_names(), m_nested_decl.get_params()),
        m_prefix(*g_nested_prefix + std::to_string(g_next_nest_id++)),
        m_tctx(env, opts, transparency_mode::Semireducible) { }

    optional<environment> operator()() {
        if (!find_nested_occ())
            return optional<environment>();

        construct_inner_decl();
        add_inner_decl();

        define_nested_inds();
        compute_inner_sizeof_simp_lemmas();

        define_nested_has_sizeofs();
        build_primitive_pack_unpack();
        define_nested_irs();
        define_nested_recursors();

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

    register_trace_class(name({"inductive_compiler", "nested", "mimic"}));
    register_trace_class(name({"inductive_compiler", "nested", "mimic", "ind"}));
    register_trace_class(name({"inductive_compiler", "nested", "mimic", "ir"}));

    register_trace_class(name({"inductive_compiler", "nested", "inner"}));
    register_trace_class(name({"inductive_compiler", "nested", "inner", "ind"}));
    register_trace_class(name({"inductive_compiler", "nested", "inner", "ir"}));

    register_trace_class(name({"inductive_compiler", "nested", "nested"}));
    register_trace_class(name({"inductive_compiler", "nested", "nested", "ind"}));
    register_trace_class(name({"inductive_compiler", "nested", "nested", "ir"}));

    register_trace_class(name({"inductive_compiler", "nested", "rec"}));
    register_trace_class(name({"inductive_compiler", "nested", "has_sizeof"}));

    register_trace_class(name({"inductive_compiler", "nested", "pack"}));
    register_trace_class(name({"inductive_compiler", "nested", "pack", "primitive"}));
    register_trace_class(name({"inductive_compiler", "nested", "pack", "nested"}));
    register_trace_class(name({"inductive_compiler", "nested", "pack", "pi"}));

    register_trace_class(name({"inductive_compiler", "nested", "unpack"}));
    register_trace_class(name({"inductive_compiler", "nested", "unpack", "primitive"}));
    register_trace_class(name({"inductive_compiler", "nested", "unpack", "nested"}));
    register_trace_class(name({"inductive_compiler", "nested", "unpack", "pi"}));

    register_trace_class(name({"inductive_compiler", "nested", "unpack_pack"}));
    register_trace_class(name({"inductive_compiler", "nested", "unpack_pack", "primitive"}));
    register_trace_class(name({"inductive_compiler", "nested", "unpack_pack", "nested"}));
    register_trace_class(name({"inductive_compiler", "nested", "unpack_pack", "pi"}));

    register_trace_class(name({"inductive_compiler", "nested", "pack_unpack"}));
    register_trace_class(name({"inductive_compiler", "nested", "pack_unpack", "primitive"}));
    register_trace_class(name({"inductive_compiler", "nested", "pack_unpack", "nested"}));
    register_trace_class(name({"inductive_compiler", "nested", "pack_unpack", "pi"}));

    register_trace_class(name({"inductive_compiler", "nested", "pack_sizeof"}));
    register_trace_class(name({"inductive_compiler", "nested", "pack_sizeof", "primitive"}));
    register_trace_class(name({"inductive_compiler", "nested", "pack_sizeof", "nested"}));
    register_trace_class(name({"inductive_compiler", "nested", "pack_sizeof", "pi"}));

    register_trace_class(name({"inductive_compiler", "nested", "force_simplify"}));
    register_trace_class(name({"inductive_compiler", "nested", "define"}));
    register_trace_class(name({"inductive_compiler", "nested", "define", "success"}));
    register_trace_class(name({"inductive_compiler", "nested", "define", "failure"}));

    g_nested_prefix = new name("_nest");
}

void finalize_inductive_compiler_nested() {
    delete g_nested_prefix;
}
}
