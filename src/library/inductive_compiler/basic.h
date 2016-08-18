/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "kernel/environment.h"
#include "frontends/lean/type_util.h"
#include "library/inductive_compiler/ginductive.h"

namespace lean {

environment add_basic_to_kernel(environment const & env, name_map<implicit_infer_kind> implicit_infer_map,
                                ginductive_decl const & decl);

environment post_process_basic(environment const & env, options const & opts, ginductive_decl const & decl);

void initialize_inductive_compiler_basic();
void finalize_inductive_compiler_basic();

}
