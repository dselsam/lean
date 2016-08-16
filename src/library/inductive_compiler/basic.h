/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "kernel/environment.h"

namespace lean {

environment tmp_add_kernel_inductive(environment const & env, buffer<name> const & lp_names,
                                     buffer<expr> const & params, expr const & ind, buffer<expr> const & intro_rules);

environment mk_basic_aux_decls(environment env, options const & opts, name const & ind_name);

void initialize_inductive_compiler_basic();
void finalize_inductive_compiler_basic();

}
