/*
Copyright (c) 2016 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include <functional>
#include "util/optional.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/abstract.h"
#include "kernel/expr_maps.h"
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/expr_lt.h"
#include "library/num.h"
#include "library/util.h"
#include "library/norm_num.h"
#include "library/defeq_canonizer.h"
#include "library/app_builder.h"
#include "library/fun_info.h"
#include "library/sorry.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/arith_normalizer/fast_arith_normalizer.h"

namespace lean {


// VM

// TODO(dhs): this is for debugging only
vm_obj tactic_fast_arith_normalize(vm_obj const & e, vm_obj const & s0) {
    tactic_state const & s   = to_tactic_state(s0);
    try {
        type_context tctx          = mk_type_context_for(s, transparency_mode::None);
        expr res                   = fast_arith_normalize(tctx, to_expr(e));
        expr pf                    = mk_eq_refl(tctx, to_expr(e));
        return mk_tactic_success(mk_vm_pair(to_obj(res), to_obj(pf)), s);
    } catch (exception & e) {
        return mk_tactic_exception(e, s);
    }
}


// Setup and teardown

void initialize_fast_arith_normalizer() {
    DECLARE_VM_BUILTIN(name({"tactic", "fast_arith_normalize"}), tactic_fast_arith_normalize);
}
void finalize_fast_arith_normalizer() {}

// Entry point

expr fast_arith_normalize(type_context & ctx, expr const & e) {
    // TODO(dhs): implement!
    return e;
}

}
