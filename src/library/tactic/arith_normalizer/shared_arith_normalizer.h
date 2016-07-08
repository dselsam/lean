/*
Copyright (c) 2016 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "library/type_context.h"

namespace lean {

#ifndef LEAN_DEFAULT_ARITH_NORMALIZE_SOM
#define LEAN_DEFAULT_ARITH_NORMALIZE_SOM true
#endif

bool get_arith_normalize_som(options const & o);

void initialize_shared_arith_normalizer();
void finalize_shared_arith_normalizer();

}
