/*
Copyright (c) 2016 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "library/type_context.h"
#include "library/tactic/simp_result.h"

namespace lean {

simp_result slow_arith_normalize(type_context & ctx, expr const & e);

void initialize_slow_arith_normalizer();
void finalize_slow_arith_normalizer();

}
