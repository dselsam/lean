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

bool curr_is_intro_rule_prefix() const {
    return m_p.curr_is_token(get_bar_tk()) || m_p.curr_is_token(get_comma_tk());
}

expr_pair parse_xinductive(parser & p, buffer<name> & lp_names, buffer<expr> & params) {
    parser::local_scope scope(p);
    auto header_pos = p.pos();
    expr l_ind = parse_single_header(p, lp_names, params);
    bool first = true;
    m_p.parse_local_notation_decl();

    buffer<expr> intro_rules;
    if (m_p.curr_is_token(get_bar_tk())) {
        m_p.next();
        while (true) {
            name intro_name = parse_intro_decl_name(ind_name);
            implicit_infer_kind k = parse_implicit_infer_modifier(m_p);
            m_implicit_infer_map.insert(intro_name, k);
            if (!m_params.empty() || m_p.curr_is_token(get_colon_tk())) {
                m_p.check_token_next(get_colon_tk(), "invalid introduction rule, ':' expected");
                expr intro_type = m_p.parse_expr();
                intro_rules.push_back(mk_intro_rule(intro_name, intro_type));
            } else {
                expr intro_type = mk_constant(ind_name);
                intro_rules.push_back(mk_intro_rule(intro_name, intro_type));
            }
            if (!curr_is_intro_rule_prefix())
                break;
            m_p.next();
        }
    }
    return to_list(intro_rules.begin(), intro_rules.end());
}
/*
    if (p.curr_is_token(get_assign_tk())) {
        p.next();
        val = p.parse_expr();
    } else if (p.curr_is_token(get_bar_tk())) {
        p.add_local(fn);
        buffer<expr> eqns;
        if (p.curr_is_token(get_none_tk())) {
            auto none_pos = p.pos();
            p.next();
            eqns.push_back(p.save_pos(mk_no_equation(), none_pos));
        } else {
            while (p.curr_is_token(get_bar_tk())) {
                eqns.push_back(parse_equation(p, fn));
            }
        }
        optional<expr_pair> R_Rwf = parse_using_well_founded(p);
        buffer<expr> fns;
        fns.push_back(fn);
        val = mk_equations(p, fns, eqns, R_Rwf, header_pos);
    } else {
        throw parser_error("invalid definition, '|' or ':=' expected", p.pos());
    }
    collect_implicit_locals(p, lp_names, params, {fn, val});
    return mk_pair(fn, val);
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
