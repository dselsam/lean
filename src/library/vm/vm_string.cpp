/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/interrupt.h"
#include "kernel/expr.h"
#include "library/sorry.h"
#include "library/constants.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_expr.h"

namespace lean {
static void to_string(vm_obj const & o, std::string & s) {
    check_system("to_string");
    if (!is_simple(o)) {
        to_string(cfield(o, 1), s);
        s += static_cast<char>(cidx(cfield(o, 0)));
    }
}

std::string to_string(vm_obj const & o) {
    std::string r;
    to_string(o, r);
    return r;
}

vm_obj string_dec_lt(vm_obj const & s1, vm_obj const & s2) {
    if (to_string(s1) < to_string(s2)) {
        return mk_vm_constructor(1, to_obj(mk_constant(get_trivial_name())));
    } else {
        return mk_vm_constructor(0, to_obj(mk_lambda(name{"contra"}, mk_constant(get_false_name()), mk_constant(get_false_name()))));
    }
}

vm_obj string_dec_le(vm_obj const & s1, vm_obj const & s2) {
    if (to_string(s1) <= to_string(s2)) {
        return mk_vm_constructor(1, to_obj(mk_constant(get_trivial_name())));
    } else {
        return mk_vm_constructor(0, to_obj(mk_lambda(name{"contra"}, mk_constant(get_false_name()), mk_constant(get_false_name()))));
    }
}

vm_obj to_obj(std::string const & str) {
    vm_obj r = mk_vm_simple(0);
    for (unsigned i = 0; i < str.size(); i++) {
        vm_obj args[2] = { mk_vm_simple(str[i]), r };
        r = mk_vm_constructor(1, 2, args);
    }
    return r;
}

void initialize_vm_string() {
    DECLARE_VM_BUILTIN(name({"string", "dec_lt"}), string_dec_lt);
    DECLARE_VM_BUILTIN(name({"string", "dec_le"}), string_dec_le);
}
void finalize_vm_string() {}

}
