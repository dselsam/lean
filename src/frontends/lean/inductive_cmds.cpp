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

static void replace_params(buffer<expr> const & params, buffer<expr> const & new_params, buffer<expr> const & old_all_exprs, buffer<expr> & new_all_exprs) {
    for (unsigned i = 0; i < old_all_exprs.size(); ++i) {
        expr new_type = replace_locals(mlocal_type(old_all_exprs[i]), params, new_params);
        new_type      = replace_locals(new_type, i, params.data(), new_params.data());
        new_all_exprs.push_back(update_mlocal(old_all_exprs[i], new_type));
    }
}

class add_xinductive_fn {
    parser &                      m_p;
    name_map<implicit_infer_kind> m_implicit_infer_map; // implicit argument inference mode

    void parse_xinductive(buffer<name> & lp_names, buffer<expr> & params, buffer<expr> & all_exprs) {
        parser::local_scope scope(m_p);
        expr l_ind = parse_single_header(m_p, lp_names, params);

        if (is_placeholder(mlocal_type(l_ind))) {
            l_ind = update_mlocal(l_ind, mk_sort(mk_level_placeholder()));
        }

        expr ty = mlocal_type(l_ind);
        while (is_pi(ty))
            ty = binding_body(ty);
        if (!is_sort(ty))
            throw parser_error("invalid inductive datatype, resultant type is not a sort", m_p.pos_of(l_ind));
        if (!lp_names.empty() && is_placeholder(sort_level(ty)))
            throw parser_error("resultant universe must be provided, when using explicit universe levels", m_p.pos_of(l_ind));

        name short_ind_name = mlocal_name(l_ind);
        l_ind = mk_local(get_namespace(m_p.env()) + short_ind_name, mlocal_type(l_ind));
        name ind_name = mlocal_name(l_ind);

        lean_trace(name({"xinductive", "parse"}),
                   tout() << mlocal_name(l_ind) << " : " << mlocal_type(l_ind) << "\n";);

        m_p.add_local_expr(short_ind_name, l_ind);
        all_exprs.push_back(l_ind);
        m_p.parse_local_notation_decl();

        // If the next token is not `|`, then the inductive type has no constructors
        if (m_p.curr_is_token(get_bar_tk())) {
            m_p.next();
            while (true) {
                name ir_name = ind_name + m_p.check_decl_id_next("invalid introduction rule, identifier expected");
                implicit_infer_kind k = parse_implicit_infer_modifier(m_p);
                m_implicit_infer_map.insert(ir_name, k);
                expr ir_type;
                if (!params.empty() || m_p.curr_is_token(get_colon_tk())) {
                    m_p.check_token_next(get_colon_tk(), "invalid introduction rule, ':' expected");
                    ir_type = m_p.parse_expr();
                } else {
                    ir_type = l_ind;
                }
                all_exprs.push_back(mk_local(ir_name, ir_type));
                lean_trace(name({"xinductive", "parse"}), tout() << ir_name << " : " << ir_type << "\n";);
                if (!m_p.curr_is_token(get_bar_tk()) && !m_p.curr_is_token(get_comma_tk()))
                    break;
                m_p.next();
            }
        }
        collect_implicit_locals(m_p, lp_names, params, all_exprs);
    }

public:
    add_xinductive_fn(parser & p): m_p(p) {}

    environment operator()() {
        buffer<name> lp_names;
        buffer<expr> params;
        buffer<expr> all_exprs;

        parse_xinductive(lp_names, params, all_exprs);

        for (expr const & p : params) {
            lean_trace(name({"xinductive", "params"}),
                       tout() << local_pp_name(p) << " : " << mlocal_type(p) << "\n";);
        }

        elaborator elab(m_p.env(), m_p.get_options(), metavar_context(), local_context());
        buffer<expr> elab_params;
        elaborate_params(elab, params, elab_params);

        buffer<expr> new_params;
        convert_params_to_kernel(elab.ctx(), elab_params, new_params);

        for (expr const & p : new_params) {
            lean_trace(name({"xinductive", "new_params"}),
                       tout() << local_pp_name(p) << " : " << mlocal_type(p) << "\n";);
        }

        buffer<expr> new_all_exprs;
        replace_params(params, new_params, all_exprs, new_all_exprs);

        for (expr & e : new_all_exprs) {
            expr new_type = elab.elaborate(mlocal_type(e));
            lean_trace(name({"xinductive", "elab"}),
                       tout() << "(" << mlocal_name(e) << ") " << mlocal_type(e) << " ==> " << new_type << "\n";);
            e = update_mlocal(e, new_type);
        }

        buffer<name> implicit_lp_names;
        buffer<expr> params_and_exprs;
        params_and_exprs.append(new_params);
        params_and_exprs.append(new_all_exprs);
        elab.finalize(params_and_exprs, implicit_lp_names, true, false);
        lp_names.append(implicit_lp_names);

        for (expr const & e : params_and_exprs) {
            lean_trace(name({"xinductive", "finalize"}), tout() << mlocal_name(e) << " : " << mlocal_type(e) << "\n";);
        }

        for (name const & lp_name : lp_names) {
            lean_trace(name({"xinductive", "lp_names"}), tout() << lp_name << "\n";);
        }

        return m_p.env();
    }
};

environment xinductive_cmd(parser & p) {
    return add_xinductive_fn(p)();
}

environment xmutual_inductive_cmd(parser & p) {
    // TODO(dhs): implement
    throw exception("xmutual_inductive_cmd not yet supported.");
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
