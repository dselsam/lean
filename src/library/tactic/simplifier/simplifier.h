/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "kernel/expr_pair.h"
#include "library/tactic/simplifier/simp_lemmas.h"

namespace lean {

// TODO(dhs): fix API
expr_pair simplify(name const & rel, expr const & e, simp_lemmas const & srss);
expr_pair simplify(name const & rel, expr const & e, simp_lemmas const & srss, expr_predicate const & simp_pred);

void initialize_simplifier();
void finalize_simplifier();

}
}
