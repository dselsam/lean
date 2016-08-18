/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "kernel/inductive/inductive.h"
#include "kernel/abstract.h"
#include "util/sexpr/option_declarations.h"
#include "library/locals.h"
#include "library/module.h"
#include "library/attribute_manager.h"
#include "library/inductive_compiler/ginductive.h"
#include "library/inductive_compiler/compiler.h"
#include "library/inductive_compiler/basic.h"
#include "library/inductive_compiler/mutual.h"

namespace lean {

environment add_inner_inductive_declaration(environment const & env, options const & opts,
                                            name_map<implicit_infer_kind> implicit_infer_map,
                                            ginductive_decl const & decl) {
    lean_assert(decl.get_inds().size() == decl.get_intro_rules().size());
    if (decl.get_inds().size() == 1) {
        // TODO(dhs): nested inductive types
        return add_basic_inductive_decl(env, opts, implicit_infer_map, decl);
    } else {
        lean_assert(decl.is_mutual());
        return add_mutual_inductive_decl(env, opts, implicit_infer_map, decl);
    }
}

environment add_inductive_declaration(environment const & old_env, options const & opts,
                                      name_map<implicit_infer_kind> implicit_infer_map,
                                      buffer<name> const & lp_names, buffer<expr> const & params,
                                      buffer<expr> const & inds, buffer<buffer<expr> > const & intro_rules) {
    environment env = add_inner_inductive_declaration(old_env, opts, implicit_infer_map, ginductive_decl(lp_names, params, inds, intro_rules));
    // TODO(dhs): register it with library/inductive
    return env;
}

void initialize_inductive_compiler() {}
void finalize_inductive_compiler() {}

}
