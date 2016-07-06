/*
Copyright (c) 2016 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "library/type_context.h"

namespace lean {

expr fast_arith_normalize(type_context & ctx, expr const & e);

void initialize_fast_arith_normalizer();
void finalize_fast_arith_normalizer();

}
