/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "kernel/inductive/inductive.h"
#include "kernel/abstract.h"
#include "library/locals.h"
#include "library/module.h"
#include "library/attribute_manager.h"
#include "library/inductive_compiler/compiler.h"

namespace lean {
using inductive::inductive_decl;
using inductive::intro_rule;
using inductive::mk_intro_rule;

environment tmp_add_kernel_inductive(environment const & env, buffer<name> const & lp_names,
                                     buffer<expr> const & params, expr const & ind, buffer<expr> const & intro_rules) {
    expr new_ind_type = Pi(params, mlocal_type(ind));
    expr c_ind = mk_app(mk_constant(mlocal_name(ind), param_names_to_levels(to_list(lp_names))), params);

    buffer<intro_rule> new_intro_rules;
    for (expr const & ir : intro_rules) {
        expr new_ir_type = Pi(params, replace_local(mlocal_type(ir), ind, c_ind));
        new_intro_rules.push_back(mk_intro_rule(mlocal_name(ir), new_ir_type));
    }
    inductive_decl decl(mlocal_name(ind), new_ind_type, to_list(new_intro_rules));
    return module::add_inductive(env, to_list(lp_names), params.size(), list<inductive_decl>(decl));
}

environment apply_modifiers(environment env, name_map<type_modifiers> const & mods) {
    mods.for_each([&](name const & n, type_modifiers const & m) {
            if (m.is_class())
                env = set_attribute(env, get_dummy_ios(), "class", n, LEAN_DEFAULT_PRIORITY, list<unsigned>(),
                                    true);
        });
    return env;
}

environment add_inductive_declaration(environment const & old_env, name_map<implicit_infer_kind> const & implicit_infer_map,
                                      name_map<type_modifiers> const & mods,
                                      buffer<name> const & lp_names, buffer<expr> const & params,
                                      buffer<expr> const & inds, buffer<buffer<expr> > const & intro_rules) {
    // TODO(dhs): mutual and nested inductive types
    lean_assert(inds.size() == 1);
    lean_assert(intro_rules.size() == 1);

    environment env = tmp_add_kernel_inductive(old_env, lp_names, params, inds[0], intro_rules[0]);
    // env = mk_aux_decls(env, decls);
    // update_declaration_index(env);
    // env = add_aliases(env, ls, locals, decls);
    // env = add_namespaces(env, decls);
    env = apply_modifiers(env, mods);
    return env;
}


void initialize_inductive_compiler() {}
void finalize_inductive_compiler() {}

}
