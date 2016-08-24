/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "library/ginductive.h"
#include "library/inductive_compiler/add_decl.h"
#include "library/inductive_compiler/compiler.h"

namespace lean {
environment add_inductive_declaration(environment const & old_env, options const & opts,
                                      name_map<implicit_infer_kind> implicit_infer_map,
                                      buffer<name> const & lp_names, buffer<expr> const & params,
                                      buffer<expr> const & inds, buffer<buffer<expr> > const & intro_rules) {
    ginductive_decl decl(lp_names, params, inds, intro_rules);
    environment env = add_inner_inductive_declaration(old_env, opts, implicit_infer_map, decl);
    env = register_ginductive_decl(env, decl);
    return env;
}
}
