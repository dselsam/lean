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
#include "library/app_builder.h"
#include "library/type_context.h"
#include "library/constructions/rec_on.h"
#include "library/constructions/induction_on.h"
#include "library/constructions/cases_on.h"
#include "library/constructions/brec_on.h"
#include "library/constructions/no_confusion.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/util.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/type_util.h"

namespace lean {

using inductive::intro_rule;

static bool curr_is_intro_rule_prefix() const {
    return m_p.curr_is_token(get_bar_tk()) || m_p.curr_is_token(get_comma_tk());
}

class add_xinductive_fn {
    name_map<implicit_infer_kind> m_implicit_infer_map; // implicit argument inference mode

    expr parse_xinductive(parser & p, buffer<name> & lp_names, buffer<expr> & params, buffer<intro_rule> & intro_rules) {
        parser::local_scope scope(p);
        buffer<expr> all_exprs; // for collect_implicit_locals
        auto header_pos = p.pos();
        expr l_ind = parse_single_header(p, lp_names, params);
        all_exprs.push_back(l_ind);
        m_p.parse_local_notation_decl();
        if (m_p.curr_is_token(get_bar_tk())) {
            m_p.next();
            while (true) {
                name intro_name = parse_intro_decl_name(ind_name);
                implicit_infer_kind k = parse_implicit_infer_modifier(m_p);
                m_implicit_infer_map.insert(intro_name, k);
                if (!m_params.empty() || m_p.curr_is_token(get_colon_tk())) {
                    m_p.check_token_next(get_colon_tk(), "invalid introduction rule, ':' expected");
                    expr intro_type = m_p.parse_expr();
                    local intro_rule = mk_intro_rule(intro_name, intro_type);
                    all_exprs.push_back(intro_rule);
                    intro_rules.push_back(intro_rule);
                } else {
                    expr intro_type = mk_constant(local_name(l_ind));
                    local intro_rule = mk_intro_rule(intro_name, intro_type);
                    all_exprs.push_back(intro_rule);
                    intro_rules.push_back(intro_rule);
                }
                if (!curr_is_intro_rule_prefix())
                    break;
                m_p.next();
            }
        }
        collect_implicit_locals(p, lp_names, params, all_exprs);
        return l_ind;
    }


public:
    environment operator()(parser & p) {
        /*
    elaborator elab(p.env(), p.get_options(), metavar_context(), local_context());
    buffer<expr> new_params;
    elaborate_params(elab, params, new_params);
    replace_params(params, new_params, fn, val);
        */


    }

}
*/

environment xinductive_cmd(parser & p) {
    // TODO(dhs): implement
    throw exception("xinductive_cmd not yet supported.");
}

environment xmutual_inductive_cmd(parser & p) {
    // TODO(dhs): implement
    throw exception("xmutual_inductive_cmd not yet supported.");
}

void register_inductive_cmds(cmd_table & r) {
    add_cmd(r, cmd_info("xinductive",        "declare an inductive datatype",        xinductive_cmd));
    add_cmd(r, cmd_info("xmutual_inductive", "declare mutually inductive datatypes", xmutual_inductive_cmd));
}

void initialize_inductive_cmds() {}
void finalize_inductive_cmds() {}

}
