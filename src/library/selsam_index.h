/*
Copyright (c) 2016 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "kernel/expr.h"

namespace lean {

optional<unsigned> is_selsam_local(expr const & e);
expr mk_selsam_local(expr const & type);

expr lift_selsam_locals(expr const & e, buffer<expr> & lifted_locals);

void initialize_selsam_index();
void finalize_selsam_index();

}
