/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "util/sexpr/option_declarations.h"
#include "library/tactic/simplifier/prop_simplifier.h"

#ifndef LEAN_DEFAULT_PROP_SIMPLIFIER_ELIM_AND
#define LEAN_DEFAULT_PROP_SIMPLIFIER_ELIM_AND false
#endif

namespace lean {

// Options
static name * g_prop_simplifier_elim_and = nullptr;

static bool get_prop_simplifier_elim_and(options const & o) {
    return o.get_bool(*g_prop_simplifier_elim_and, LEAN_DEFAULT_PROP_SIMPLIFIER_ELIM_AND);
}

prop_simplifier_options::prop_simplifier_options(options const & o):
    m_elim_and(get_prop_simplifier_elim_and(o)) {}






// Setup and teardown
void initialize_prop_simplifier() {
    // Option names
    g_prop_simplifier_elim_and     = new name{"prop_simplifier", "elim_and"};

    // Register options
    register_bool_option(*g_prop_simplifier_elim_and, LEAN_DEFAULT_PROP_SIMPLIFIER_ELIM_AND,
                         "(prop_simplifier) (and a b c) ==> (not (or (not a) (not b) (not c)))");
}

void finalize_prop_simplifier() {
    // Option names
    delete g_prop_simplifier_elim_and;
}
}
