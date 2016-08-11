/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "library/inductive_compiler/ginductive.h"

namespace lean {

static bool is_nested_inductive_decl(environment const & env, ginductive_decl const & gdecl) {




}

static bool is_basic_inductive_decl(environment const & env, ginductive_decl const & gdecl) {




}






environment register_ginductive_decl(environment const & env, ginductive_decl const & gdecl) {
    throw exception("register_ginductive_decl not yet implemented");
}

void initialize_ginductive() {}
void finalize_ginductive() {}
}
