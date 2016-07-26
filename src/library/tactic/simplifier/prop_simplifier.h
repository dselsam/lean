/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "library/tactic/simplifier/simplifier.h"

namespace lean {









optional<expr> fast_simplify_and(type_context & tctx, buffer<expr> & args);
optional<expr> fast_simplify_or(type_context & tctx, buffer<expr> & args);
optional<expr> fast_simplify_not(type_context & tctx, buffer<expr> & args);

void initialize_prop_simplifier();
void finalize_prop_simplifier();

}
