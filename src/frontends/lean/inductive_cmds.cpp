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

static void check_ind_type(parser & p, expr const & ind, bool explicit_levels) {
    expr ty = mlocal_type(ind);
    while (is_pi(ty))
        ty = binding_body(ty);
    if (!is_sort(ty))
        throw parser_error("invalid inductive datatype, resultant type is not a sort", p.pos_of(ind));
    if (explicit_levels && is_placeholder(sort_level(ty)))
        throw parser_error("resultant universe must be provided, when using explicit universe levels", p.pos_of(ind));
}

static void parse_intro_rules(parser & p, name_map<implicit_infer_kind> & implicit_infer_map, bool has_params, expr const & ind, buffer<expr> & intro_rules) {
    // If the next token is not `|`, then the inductive type has no constructors
    if (p.curr_is_token(get_bar_tk())) {
        p.next();
        while (true) {
            name ir_name = get_namespace(p.env()) + mlocal_name(ind) + p.check_decl_id_next("invalid introduction rule, identifier expected");
            implicit_infer_map.insert(ir_name, parse_implicit_infer_modifier(p));
            expr ir_type;
            if (has_params || p.curr_is_token(get_colon_tk())) {
                p.check_token_next(get_colon_tk(), "invalid introduction rule, ':' expected");
                ir_type = p.parse_expr();
            } else {
                ir_type = ind;
            }
            intro_rules.push_back(mk_local(ir_name, ir_type));
            lean_trace(name({"xinductive", "parse"}), tout() << ir_name << " : " << ir_type << "\n";);
            if (!p.curr_is_token(get_bar_tk()) && !p.curr_is_token(get_comma_tk()))
                break;
            p.next();
        }
    }
}

static environment elaborate_inductive_decls(environment const & env, options const & opts,
                                             buffer<name> & lp_names,
                                             buffer<expr> const & params, buffer<expr> const & inds, buffer<buffer<expr> > const & intro_rules,
                                             buffer<expr> & new_params, buffer<expr> & new_inds, buffer<buffer<expr> > & new_intro_rules) {
    elaborator elab(env, opts, metavar_context(), local_context());
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
    buffer<expr> all_exprs;
    collect_all_exprs(new_params, new_inds, new_intro_rules, all_exprs);

    elab.finalize(all_exprs, implicit_lp_names, true, false);
    lp_names.append(implicit_lp_names);

    for (expr const & e : all_exprs) {
        lean_trace(name({"xinductive", "finalize"}), tout() << mlocal_name(e) << " : " << mlocal_type(e) << "\n";);
    }

    for (name const & lp_name : lp_names) {
        lean_trace(name({"xinductive", "lp_names"}), tout() << lp_name << "\n";);
    }

    return elab.env();
}

static expr parse_xinductive(parser & p, name_map<implicit_infer_kind> & implicit_infer_map, buffer<name> & lp_names, buffer<expr> & params, buffer<expr> & intro_rules) {
    parser::local_scope scope(p);
    expr ind = parse_single_header(p, lp_names, params);

    if (is_placeholder(mlocal_type(ind))) {
        ind = update_mlocal(ind, mk_sort(mk_level_placeholder()));
    }

    check_ind_type(p, ind, !lp_names.empty());
    name short_ind_name = mlocal_name(ind);
    ind = mk_local(get_namespace(p.env()) + short_ind_name, mlocal_type(ind));
    name ind_name = mlocal_name(ind);

    lean_trace(name({"xinductive", "parse"}),
               tout() << mlocal_name(ind) << " : " << mlocal_type(ind) << "\n";);

    p.add_local_expr(short_ind_name, ind);
    p.parse_local_notation_decl();

    parse_intro_rules(p, implicit_infer_map, !params.empty(), ind, intro_rules);

    buffer<expr> ind_intro_rules;
    ind_intro_rules.push_back(ind);
    ind_intro_rules.append(intro_rules);
    collect_implicit_locals(p, lp_names, params, ind_intro_rules);
    return ind;
}

static void parse_xmutual_inductive(parser & p, name_map<implicit_infer_kind> & implicit_infer_map,
                                    buffer<name> & lp_names, buffer<expr> & params, buffer<expr> & inds, buffer<buffer<expr> > & intro_rules) {
    parser::local_scope scope(p);
    buffer<expr> pre_inds;
    parse_mutual_header(p, lp_names, pre_inds, params);
    p.parse_local_notation_decl();

    for (expr const & pre_ind : pre_inds) {
        expr ind_type = parse_inner_header(p, local_pp_name(pre_ind));
        lean_trace(name({"xinductive", "parse"}), tout() << mlocal_name(pre_ind) << " : " << ind_type << "\n";);
        intro_rules.emplace_back();
        parse_intro_rules(p, implicit_infer_map, !params.empty(), pre_ind, intro_rules.back());
        expr ind = mk_local(get_namespace(p.env()) + mlocal_name(pre_ind), ind_type);
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

    collect_implicit_locals(p, lp_names, params, all_inds_intro_rules);
}

environment xinductive_cmd(parser & p) {
    name_map<implicit_infer_kind> implicit_infer_map;
    buffer<name> lp_names;
    buffer<expr> params;
    buffer<expr> inds;
    buffer<buffer<expr> > intro_rules;
    intro_rules.emplace_back();
    inds.push_back(parse_xinductive(p, implicit_infer_map, lp_names, params, intro_rules.back()));

    buffer<expr> new_params;
    buffer<expr> new_inds;
    buffer<buffer<expr> > new_intro_rules;
    environment env = elaborate_inductive_decls(p.env(), p.get_options(), lp_names, params, inds, intro_rules, new_params, new_inds, new_intro_rules);
    return env;
}

environment xmutual_inductive_cmd(parser & p) {
    name_map<implicit_infer_kind> implicit_infer_map;
    buffer<name> lp_names;
    buffer<expr> params;
    buffer<expr> inds;
    buffer<buffer<expr> > intro_rules;

    parse_xmutual_inductive(p, implicit_infer_map, lp_names, params, inds, intro_rules);

    buffer<expr> new_params;
    buffer<expr> new_inds;
    buffer<buffer<expr> > new_intro_rules;
    environment env = elaborate_inductive_decls(p.env(), p.get_options(), lp_names, params, inds, intro_rules, new_params, new_inds, new_intro_rules);

    return env;
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
