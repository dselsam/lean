/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "kernel/environment.h"

namespace lean {

environment mk_basic_aux_decls(environment env, buffer<name> const & lp_names, buffer<expr> const & params, expr const & ind, buffer<expr> const & intro_rules);

void initialize_inductive_compiler_basic();
void finalize_inductive_compiler_basic();

}
