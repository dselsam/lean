/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "frontends/smt2/init_module.h"
#include "frontends/smt2/scanner.h"

namespace lean {

void initialize_frontend_smt2_module() {
    smt2::initialize_scanner();
}

void finalize_frontend_smt2_module() {
    smt2::finalize_scanner();
}

}
