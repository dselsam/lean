/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "library/type_context.h"
#include "library/tactic/simp_result.h"
#include "library/tactic/simplifier/simp_lemmas.h"

namespace lean {

simp_result rewrite(type_context & tctx, simp_lemmas const & lemmas, expr const & e);

void initialize_simp_rewrite();
void finalize_simp_rewrite();
}
