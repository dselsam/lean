/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "library/type_context.h"
#include "library/tactic/simplifier/rewrite.h"

namespace lean {

simp_result rewrite(type_context & tctx, simp_lemmas const & lemmas, expr const & e) {
    throw exception("NYI");
    return simp_result(e);
}

void initialize_simp_rewrite() {}
void finalize_simp_rewrite() {}
}
