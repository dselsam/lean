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
#include "library/inductive_compiler/basic.h"

namespace lean {

using inductive::inductive_decl;
using inductive::intro_rule;
using inductive::mk_intro_rule;

environment tmp_add_kernel_inductive(environment const & env, name_map<implicit_infer_kind> implicit_infer_map,
                                     buffer<name> const & lp_names,
                                     buffer<expr> const & params, expr const & ind, buffer<expr> const & intro_rules) {
    expr new_ind_type = Pi(params, mlocal_type(ind));
    expr c_ind = mk_app(mk_constant(mlocal_name(ind), param_names_to_levels(to_list(lp_names))), params);

    buffer<intro_rule> new_intro_rules;
    for (expr const & ir : intro_rules) {
        expr new_ir_type = Pi(params, replace_local(mlocal_type(ir), ind, c_ind));
        implicit_infer_kind k = *implicit_infer_map.find(mlocal_name(ir));
        new_intro_rules.push_back(mk_intro_rule(mlocal_name(ir), infer_implicit_params(new_ir_type, params.size(), k)));
    }
    inductive_decl decl(mlocal_name(ind), new_ind_type, to_list(new_intro_rules));
    return module::add_inductive(env, to_list(lp_names), params.size(), list<inductive_decl>(decl));
}

environment mk_basic_aux_decls(environment env, options const & opts, name const & ind_name) {
    bool has_unit = has_poly_unit_decls(env);
    bool has_eq   = has_eq_decls(env);
    bool has_heq  = has_heq_decls(env);
    bool has_prod = has_prod_decls(env);
    bool has_lift = has_lift_decls(env);

    env = mk_rec_on(env, ind_name);
    if (env.impredicative())
        env = mk_induction_on(env, ind_name);

    if (has_unit) {
        env = mk_cases_on(env, ind_name);
        if (has_eq && ((env.prop_proof_irrel() && has_heq) || (!env.prop_proof_irrel() && has_lift))) {
                env = mk_no_confusion(env, ind_name);
            if (has_prod) {
                env = mk_below(env, ind_name);
                if (env.impredicative()) {
                    env = mk_ibelow(env, ind_name);
                }
            }
        }
    }

    if (has_unit && has_prod) {
        env = mk_brec_on(env, ind_name);
        if (env.impredicative()) {
            env = mk_binduction_on(env, ind_name);
        }
    }
    return env;
}

void initialize_inductive_compiler_basic() {}
void finalize_inductive_compiler_basic() {}

}
