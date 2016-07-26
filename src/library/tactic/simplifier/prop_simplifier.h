/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "library/tactic/simplifier/simplifier.h"

namespace lean {









expr fast_simplify_and(buffer<expr> & args);
expr fast_simplify_or(buffer<expr> & args);

void initialize_prop_simplifier();
void finalize_prop_simplifier();

}
