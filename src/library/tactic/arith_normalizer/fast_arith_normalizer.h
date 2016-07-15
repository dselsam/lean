/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "library/tactic/arith_normalizer/util.h"

namespace lean {

expr fast_arith_normalize(type_context & tctx, expr const & e, arith_normalize_options const & options);

void initialize_fast_arith_normalizer();
void finalize_fast_arith_normalizer();

}
