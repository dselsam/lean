/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
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

environment mk_basic_aux_decls(environment env, buffer<name> const & lp_names, buffer<expr> const & params, expr const & ind, buffer<expr> const & intro_rules) {
    /*
    bool has_unit = has_poly_unit_decls(env);
    bool has_eq   = has_eq_decls(env);
    bool has_heq  = has_heq_decls(env);
    bool has_prod = has_prod_decls(env);
    bool has_lift = has_lift_decls(env);
    options opts  = m_p.get_options();


    for (inductive_decl const & d : decls) {
        name const & n = inductive_decl_name(d);
        pos_info pos   = *m_decl_pos_map.find(n);
        if (gen_rec_on) {
            env = mk_rec_on(env, n);
            save_def_info(name(n, "rec_on"), pos);
        }
        if (gen_rec_on && env.impredicative()) {
            env = mk_induction_on(env, n);
            save_def_info(name(n, "induction_on"), pos);
        }
        if (has_unit) {
            if (gen_cases_on) {
                env = mk_cases_on(env, n);
                save_def_info(name(n, "cases_on"), pos);
            }
            if (gen_cases_on && gen_no_confusion && has_eq && ((env.prop_proof_irrel() && has_heq) || (!env.prop_proof_irrel() && has_lift))) {
                env = mk_no_confusion(env, n);
                save_if_defined(name{n, "no_confusion_type"}, pos);
                save_if_defined(name(n, "no_confusion"), pos);
            }
            if (gen_brec_on && has_prod) {
                env = mk_below(env, n);
                save_if_defined(name{n, "below"}, pos);
                if (env.impredicative()) {
                    env = mk_ibelow(env, n);
                    save_if_defined(name(n, "ibelow"), pos);
                }
            }
        }
    }
    for (inductive_decl const & d : decls) {
        name const & n = inductive_decl_name(d);
        pos_info pos   = *m_decl_pos_map.find(n);
        if (gen_brec_on && has_unit && has_prod) {
            env = mk_brec_on(env, n);
            save_if_defined(name{n, "brec_on"}, pos);
            if (env.impredicative()) {
                env = mk_binduction_on(env, n);
                save_if_defined(name(n, "binduction_on"), pos);
            }
        }
    }
    */
    return env;
}

void initialize_inductive_compiler_basic() {}
void finalize_inductive_compiler_basic() {}

}
