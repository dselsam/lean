/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "kernel/expr.h"
#include "library/tactic/simp_result.h"

namespace lean {

expr mk_flat_congr_simp_macro(expr const & assoc, expr const & e_orig, buffer<simp_result> const & results, simp_result const & r_simp);


void initialize_simp_util();
void finalize_simp_util();

}
