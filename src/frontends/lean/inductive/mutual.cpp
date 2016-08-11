/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "kernel/environment.h"
#include "frontends/lean/inductive/mutual.h"

namespace lean {

basic_inductive_decl compile_mutual_to_basic(mutual_inductive_decl const & mut_decl) {
    throw exception("TODO(dhs): implement");
}

void initialize_inductive_mutual() {}
void finalize_inductive_mutual() {}
}
