/*
Copyright (c) 2016 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "library/type_context.h"
#include "library/tactic/simp_result.h"

namespace lean {

simp_result arith_normalize(type_context & tctx, expr const & e);

void initialize_arith_normalizer();
void finalize_arith_normalizer();

}
