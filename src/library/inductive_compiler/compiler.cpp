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
#include "library/inductive_compiler/basic.h"

namespace lean {

environment add_inductive_declaration(environment const & old_env,
                                      buffer<name> const & lp_names, buffer<expr> const & params,
                                      buffer<expr> const & inds, buffer<buffer<expr> > const & intro_rules) {
    // TODO(dhs): mutual and nested inductive types
    lean_assert(inds.size() == 1);
    lean_assert(intro_rules.size() == 1);

    environment env = tmp_add_kernel_inductive(old_env, lp_names, params, inds[0], intro_rules[0]);
    return env;
}


void initialize_inductive_compiler() {}
void finalize_inductive_compiler() {}

}
