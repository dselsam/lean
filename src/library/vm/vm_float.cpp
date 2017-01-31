/*
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include <iostream>
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"

namespace lean {

struct vm_float : public vm_external {
    float m_val;
    vm_float(float const & x): m_val(x) {}
    virtual ~vm_float() {}
    virtual void dealloc() override { this->~vm_float(); get_vm_allocator().deallocate(sizeof(vm_float), this); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_float(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_float))) vm_float(m_val); }
};

vm_obj to_obj(float const & x) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_float))) vm_float(x));
}

float to_float(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_float*>(to_external(o)));
    return static_cast<vm_float*>(to_external(o))->m_val;
}

vm_obj float_zero() { return to_obj(0.0); }
vm_obj float_one() { return to_obj(1.0); }

vm_obj float_neg(vm_obj const & x) { return to_obj(-to_float(x)); }
vm_obj float_inv(vm_obj const & x) { return to_obj(1.0/to_float(x)); }
vm_obj float_exp(vm_obj const & x) { return to_obj(exp(to_float(x))); }
vm_obj float_log(vm_obj const & x) { return to_obj(log(to_float(x))); }

vm_obj float_add(vm_obj const & x, vm_obj const & y) { return to_obj(to_float(x) + to_float(y)); }
vm_obj float_mul(vm_obj const & x, vm_obj const & y) { return to_obj(to_float(x) * to_float(y)); }
vm_obj float_sub(vm_obj const & x, vm_obj const & y) { return to_obj(to_float(x) - to_float(y)); }
vm_obj float_div(vm_obj const & x, vm_obj const & y) { return to_obj(to_float(x) / to_float(y)); }

vm_obj float_to_string(vm_obj const & x) {
    std::ostringstream out;
    out << to_float(x);
    return to_obj(out.str());
}

void initialize_vm_float() {
    DECLARE_VM_BUILTIN(name({"float", "zero"}),       float_zero);
    DECLARE_VM_BUILTIN(name({"float", "one"}),        float_one);
    DECLARE_VM_BUILTIN(name({"float", "neg"}),        float_neg);
    DECLARE_VM_BUILTIN(name({"float", "inv"}),        float_inv);
    DECLARE_VM_BUILTIN(name({"float", "exp"}),        float_exp);
    DECLARE_VM_BUILTIN(name({"float", "log"}),        float_log);
    DECLARE_VM_BUILTIN(name({"float", "add"}),        float_add);
    DECLARE_VM_BUILTIN(name({"float", "mul"}),        float_mul);
    DECLARE_VM_BUILTIN(name({"float", "sub"}),        float_sub);
    DECLARE_VM_BUILTIN(name({"float", "div"}),        float_div);
    DECLARE_VM_BUILTIN(name({"float", "to_string"}),  float_to_string);
}

void finalize_vm_float() {}

}
