/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "library/tactic/arith_normalizer/util.h"
#include "library/tactic/arith_normalizer/arith_instance_manager.h"
#include "library/tactic/arith_normalizer/fast_arith_normalizer.h"
#include "library/tactic/arith_normalizer/arith_normalizer.h"

namespace lean {

void initialize_arith_normalizer_module() {
    initialize_arith_normalizer_instance_manager();
    initialize_arith_normalizer_util();
    initialize_arith_normalizer();
    initialize_fast_arith_normalizer();
}

void finalize_arith_normalizer_module() {
    finalize_fast_arith_normalizer();
    finalize_arith_normalizer();
    finalize_arith_normalizer_util();
    finalize_arith_normalizer_instance_manager();
}
}
