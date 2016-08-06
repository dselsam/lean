/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include <string>
#include "util/sstream.h"
#include "kernel/expr.h"
#include "util/numerics/mpq.h"
#include "library/num.h"
#include "library/mpq_macro.h"
#include "library/type_context.h"
#include "library/arith_instance_manager.h"

namespace lean {

expr mpq2expr(arith_instance_info_ref const & info, mpq const & q);

expr mk_mpq_macro(mpq const & q, expr const & type);

bool is_mpq_macro(expr const & e);
bool is_mpq_macro(expr const & e, mpq & q);

void initialize_tactic_num();
void finalize_tactic_num();
}
