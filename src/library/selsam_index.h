/*
Copyright (c) 2016 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "kernel/expr.h"
#include "kernel/expr_sets.h"

namespace lean {

optional<unsigned> is_selsam_local(expr const & e);
expr mk_selsam_local(expr const & type);

bool has_selsam_local(expr const & e);

expr lift_selsam_locals(expr const & e);
expr lower_selsam_locals(expr const & e);

bool selsam_local_eq_upto_index(expr const & e1, expr const & e2);

expr_struct_set all_locals_at_selsam_index0(expr const & e);

void initialize_selsam_index();
void finalize_selsam_index();

}
