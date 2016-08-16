/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include <algorithm>
#include <library/attribute_manager.h>
#include "util/sstream.h"
#include "util/name_map.h"
#include "util/fresh_name.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/replace_fn.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "kernel/abstract.h"
#include "kernel/free_vars.h"
#include "library/scoped_ext.h"
#include "library/locals.h"
#include "library/deep_copy.h"
#include "library/placeholder.h"
#include "library/aliases.h"
#include "library/protected.h"
#include "library/explicit.h"
#include "library/reducible.h"
#include "library/class.h"
#include "library/util.h"
#include "library/trace.h"
#include "library/app_builder.h"
#include "library/type_context.h"
#include "library/constructions/rec_on.h"
#include "library/constructions/induction_on.h"
#include "library/constructions/cases_on.h"
#include "library/constructions/brec_on.h"
#include "library/constructions/no_confusion.h"
#include "library/inductive_compiler/compiler.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/decl_util.h"
#include "frontends/lean/util.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/type_util.h"

namespace lean {

static void convert_params_to_kernel(type_context & tctx, buffer<expr> const & lctx_params, buffer<expr> & kernel_params) {
    for (unsigned i = 0; i < lctx_params.size(); ++i) {
        expr new_type = replace_locals(tctx.infer(lctx_params[i]), i, lctx_params.data(), kernel_params.data());
        kernel_params.push_back(update_mlocal(lctx_params[i], new_type));
    }
}

static void replace_params(buffer<expr> const & params, buffer<expr> const & new_params, expr const & ind, expr const & new_ind,
                           buffer<expr> const & intro_rules, buffer<expr> & new_intro_rules) {
    for (expr const & ir : intro_rules) {
        expr new_type = replace_locals(mlocal_type(ir), params, new_params);
        new_type = replace_local(new_type, ind, new_ind);
        new_intro_rules.push_back(update_mlocal(ir, new_type));
    }
}

static void replace_params(buffer<expr> const & params, buffer<expr> const & new_params, buffer<expr> const & inds, buffer<expr> const & new_inds,
                           buffer<expr> const & intro_rules, buffer<expr> & new_intro_rules) {
    for (expr const & ir : intro_rules) {
        expr new_type = replace_locals(mlocal_type(ir), params, new_params);
        new_type = replace_locals(new_type, inds, new_inds);
        new_intro_rules.push_back(update_mlocal(ir, new_type));
    }
}

static void collect_all_exprs(buffer<expr> const & params, buffer<expr> const & inds, buffer<buffer<expr> > const & intro_rules, buffer<expr> & all_exprs) {
    all_exprs.append(params);
    all_exprs.append(inds);
    for (buffer<expr> const & irs : intro_rules)
        all_exprs.append(irs);
}

static void collect_all_exprs(buffer<expr> const & params, expr const & ind, buffer<expr> const & intro_rules, buffer<expr> & all_exprs) {
    all_exprs.append(params);
    all_exprs.push_back(ind);
    all_exprs.append(intro_rules);
}

class inductive_cmd_fn {
    parser &                        m_p;
    buffer<name>                    m_lp_names;
    name_map<implicit_infer_kind>   m_implicit_infer_map;
    bool                            m_explicit_levels; // true if the user is providing explicit universe levels
    level                           m_u; // temporary auxiliary global universe used for inferring the result
                                         // universe of an inductive datatype declaration.

    void check_ind_type(expr const & ind) {
        expr ty = mlocal_type(ind);
        while (is_pi(ty))
            ty = binding_body(ty);
        if (!is_sort(ty))
            throw parser_error("invalid inductive datatype, resultant type is not a sort", m_p.pos_of(ind));
        if (m_explicit_levels && is_placeholder(sort_level(ty)))
            throw parser_error("resultant universe must be provided, when using explicit universe levels", m_p.pos_of(ind));
    }

    void parse_intro_rules(bool has_params, expr const & ind, buffer<expr> & intro_rules, bool prepend_ns) {
        // If the next token is not `|`, then the inductive type has no constructors
        if (m_p.curr_is_token(get_bar_tk())) {
            m_p.next();
            while (true) {
                name ir_name = mlocal_name(ind) + m_p.check_decl_id_next("invalid introduction rule, identifier expected");
                if (prepend_ns)
                    ir_name = get_namespace(m_p.env()) + ir_name;
                m_implicit_infer_map.insert(ir_name, parse_implicit_infer_modifier(m_p));
                expr ir_type;
                if (has_params || m_p.curr_is_token(get_colon_tk())) {
                    m_p.check_token_next(get_colon_tk(), "invalid introduction rule, ':' expected");
                    ir_type = m_p.parse_expr();
                } else {
                    ir_type = ind;
                }
                intro_rules.push_back(mk_local(ir_name, ir_type));
                lean_trace(name({"xinductive", "parse"}), tout() << ir_name << " : " << ir_type << "\n";);
                if (!m_p.curr_is_token(get_bar_tk()) && !m_p.curr_is_token(get_comma_tk()))
                    break;
                m_p.next();
            }
        }
    }

    environment elaborate_inductive_decls(buffer<expr> const & params, buffer<expr> const & inds, buffer<buffer<expr> > const & intro_rules,
                                          buffer<expr> & new_params, buffer<expr> & new_inds, buffer<buffer<expr> > & new_intro_rules) {
        elaborator elab(m_p.env(), m_p.get_options(), metavar_context(), local_context());
        buffer<expr> elab_params;
        elaborate_params(elab, params, elab_params);

        convert_params_to_kernel(elab.ctx(), elab_params, new_params);

        for (expr const & ind : inds)
            new_inds.push_back(update_mlocal(ind, elab.elaborate(replace_locals(mlocal_type(ind), params, new_params))));

        for (buffer<expr> const & irs : intro_rules) {
            new_intro_rules.emplace_back();
            replace_params(params, new_params, inds, new_inds, irs, new_intro_rules.back());
            for (expr & new_ir : new_intro_rules.back())
                new_ir = update_mlocal(new_ir, elab.elaborate(mlocal_type(new_ir)));
        }

        buffer<name> implicit_lp_names;

        // TODO(dhs): this is a crazy (temporary) hack around the rigid elaborator API
        buffer<unsigned> offsets;
        buffer<expr> all_exprs;
        offsets.push_back(new_params.size());
        all_exprs.append(new_params);
        offsets.push_back(new_inds.size());
        all_exprs.append(new_inds);
        for (buffer<expr> & irs : new_intro_rules) {
            offsets.push_back(irs.size());
            all_exprs.append(irs);
        }

        elab.finalize(all_exprs, implicit_lp_names, true, false);
        m_lp_names.append(implicit_lp_names);

        new_params.clear();
        new_inds.clear();
        new_intro_rules.clear();

        for (unsigned i = 0; i < offsets[0]; ++i)
            new_params.push_back(all_exprs[i]);
        for (unsigned i = 0; i < offsets[1]; ++i)
            new_inds.push_back(all_exprs[offsets[0] + i]);
        for (unsigned i = 2; i < offsets.size(); ++i) {
            new_intro_rules.emplace_back();
            unsigned offset = offsets[0] + offsets[1];
            for (unsigned j = 0; j < offsets[i]; ++j) {
                new_intro_rules.back().push_back(all_exprs[offset + j]);
            }
            offset += offsets[i];
        }

        for (expr const & e : all_exprs) {
            lean_trace(name({"xinductive", "finalize"}),
                       tout() << mlocal_name(e) << " : " << mlocal_type(e) << "\n";);
        }

        return elab.env();
    }

    expr parse_xinductive(buffer<expr> & params, buffer<expr> & intro_rules) {
        parser::local_scope scope(m_p);
        expr ind = parse_single_header(m_p, m_lp_names, params);
        m_explicit_levels = !m_lp_names.empty();

        // TODO(dhs): do this later?
//        if (is_placeholder(mlocal_type(ind))) {
//            ind = update_mlocal(ind, mk_sort(mk_level_placeholder()));
//       }

        check_ind_type(ind);
        name short_ind_name = mlocal_name(ind);
        ind = mk_local(get_namespace(m_p.env()) + short_ind_name, mlocal_type(ind));
        name ind_name = mlocal_name(ind);

        lean_trace(name({"xinductive", "parse"}),
                   tout() << mlocal_name(ind) << " : " << mlocal_type(ind) << "\n";);

        m_p.add_local_expr(short_ind_name, ind);
        m_p.parse_local_notation_decl();

        parse_intro_rules(!params.empty(), ind, intro_rules, false);

        buffer<expr> ind_intro_rules;
        ind_intro_rules.push_back(ind);
        ind_intro_rules.append(intro_rules);
        collect_implicit_locals(m_p, m_lp_names, params, ind_intro_rules);
        return ind;
    }

    void parse_xmutual_inductive(buffer<expr> & params, buffer<expr> & inds, buffer<buffer<expr> > & intro_rules) {
        parser::local_scope scope(m_p);
        buffer<expr> pre_inds;
        parse_mutual_header(m_p, m_lp_names, pre_inds, params);
        m_explicit_levels = !m_lp_names.empty();
        m_p.parse_local_notation_decl();

        for (expr const & pre_ind : pre_inds) {
            expr ind_type = parse_inner_header(m_p, local_pp_name(pre_ind));
            check_ind_type(update_mlocal(pre_ind, ind_type));
            lean_trace(name({"xinductive", "parse"}), tout() << mlocal_name(pre_ind) << " : " << ind_type << "\n";);
            intro_rules.emplace_back();
            parse_intro_rules(!params.empty(), pre_ind, intro_rules.back(), true);
            expr ind = mk_local(get_namespace(m_p.env()) + mlocal_name(pre_ind), ind_type);
            inds.push_back(ind);
        }

        for (buffer<expr> & irs : intro_rules) {
            for (expr & ir : irs) {
                ir = replace_locals(ir, pre_inds, inds);
            }
        }

        buffer<expr> all_inds_intro_rules;
        all_inds_intro_rules.append(inds);
        for (buffer<expr> const & irs : intro_rules)
            all_inds_intro_rules.append(irs);

        collect_implicit_locals(m_p, m_lp_names, params, all_inds_intro_rules);
    }
public:
    inductive_cmd_fn(parser & p): m_p(p) {}

    environment inductive_cmd() {
        buffer<expr> params;
        buffer<expr> inds;
        buffer<buffer<expr> > intro_rules;
        intro_rules.emplace_back();
        inds.push_back(parse_xinductive(params, intro_rules.back()));

        buffer<expr> new_params;
        buffer<expr> new_inds;
        buffer<buffer<expr> > new_intro_rules;
        environment env = elaborate_inductive_decls(params, inds, intro_rules, new_params, new_inds, new_intro_rules);

        return add_inductive_declaration(env, m_implicit_infer_map, m_lp_names, new_params, new_inds, new_intro_rules);
    }

    environment mutual_inductive_cmd() {
        buffer<expr> params;
        buffer<expr> inds;
        buffer<buffer<expr> > intro_rules;

        parse_xmutual_inductive(params, inds, intro_rules);

        buffer<expr> new_params;
        buffer<expr> new_inds;
        buffer<buffer<expr> > new_intro_rules;
        environment env = elaborate_inductive_decls(params, inds, intro_rules, new_params, new_inds, new_intro_rules);
        return add_inductive_declaration(env, m_implicit_infer_map, m_lp_names, new_params, new_inds, new_intro_rules);
    }
};

environment xinductive_cmd(parser & p) {
    return inductive_cmd_fn(p).inductive_cmd();
}

environment xmutual_inductive_cmd(parser & p) {
    return inductive_cmd_fn(p).mutual_inductive_cmd();
}

void register_inductive_cmds(cmd_table & r) {
    add_cmd(r, cmd_info("xinductive",        "declare an inductive datatype",        xinductive_cmd));
    add_cmd(r, cmd_info("xmutual_inductive", "declare mutually inductive datatypes", xmutual_inductive_cmd));
}

void initialize_inductive_cmds() {
    register_trace_class("xinductive");
    register_trace_class(name({"xinductive", "parse"}));
    register_trace_class(name({"xinductive", "elab"}));
    register_trace_class(name({"xinductive", "params"}));
    register_trace_class(name({"xinductive", "new_params"}));
    register_trace_class(name({"xinductive", "finalize"}));
    register_trace_class(name({"xinductive", "lp_names"}));
}

void finalize_inductive_cmds() {}

}
