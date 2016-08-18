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

environment compile_ginductive_decl(environment const & old_env, options const & opts,
                                    name_map<implicit_infer_kind> implicit_infer_map,
                                    ginductive_decl const & decl) {
    lean_assert(decl.get_inds().size() == decl.get_intro_rules().size());
    if (decl.get_inds().size() == 1) {
        // TODO(dhs): nested inductive types
        environment env = add_basic_to_kernel(old_env, implicit_infer_map, decl);
        return post_process_basic(env, opts, decl);
    } else {
        // Mutual, for now
        lean_assert(decl.is_mutual());
        auto basic_decl_aux = compile_mutual_to_basic(old_env, decl);
        ginductive_decl & basic_decl = basic_decl_aux.first;
        mutual_decl_aux & mutual_aux = basic_decl_aux.second;

        lean_assert(!basic_decl.is_mutual());
        environment env = compile_ginductive_decl(old_env, opts, implicit_infer_map, basic_decl);
        return post_process_mutual(env, opts, implicit_infer_map, decl, basic_decl, mutual_aux);
    }
}

environment add_inductive_declaration(environment const & old_env, options const & opts,
                                      name_map<implicit_infer_kind> implicit_infer_map,
                                      buffer<name> const & lp_names, buffer<expr> const & params,
                                      buffer<expr> const & inds, buffer<buffer<expr> > const & intro_rules) {
    return compile_ginductive_decl(old_env, opts, implicit_infer_map, ginductive_decl(lp_names, params, inds, intro_rules));
}

void initialize_inductive_compiler() {}
void finalize_inductive_compiler() {}

}
