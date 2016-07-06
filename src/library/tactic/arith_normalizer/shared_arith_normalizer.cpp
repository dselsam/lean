/*
Copyright (c) 2016 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/tactic/arith_normalizer/shared_arith_normalizer.h"

namespace lean {

// Options shared by fast and slow arith-normalizers

name * g_arith_normalize_som = nullptr;

bool get_arith_normalize_som(options const & o) {
    return o.get_bool(*g_arith_normalize_som, LEAN_DEFAULT_ARITH_NORMALIZE_SOM);
}


// Setup and teardown

void initialize_shared_arith_normalizer() {
    g_arith_normalize_som = new name{"arith_normalize", "som"};
}

void finalize_shared_arith_normalizer() {
    delete g_arith_normalize_som;
}


}
