/*
Copyright (c) 2016 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/tactic/arith_normalizer/shared_arith_normalizer.h"
#include "library/tactic/arith_normalizer/fast_arith_normalizer.h"
#include "library/tactic/arith_normalizer/slow_arith_normalizer.h"

namespace lean {

void initialize_arith_normalizer_module() {
    initialize_shared_arith_normalizer();
    initialize_fast_arith_normalizer();
    initialize_slow_arith_normalizer();
}

void finalize_arith_normalizer_module() {
    finalize_slow_arith_normalizer();
    finalize_fast_arith_normalizer();
    finalize_shared_arith_normalizer();
}
}
