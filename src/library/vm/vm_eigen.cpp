/*
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include <iostream>
#include "library/vm/vm.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_eigen.h"

namespace lean {

struct vm_eigen : public vm_external {
    Eigen::ArrayXf m_val;
    vm_eigen(Eigen::ArrayXf const & v): m_val(v) {}
    virtual ~vm_eigen() {}
    virtual void dealloc() override { this->~vm_eigen(); get_vm_allocator().deallocate(sizeof(vm_eigen), this); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_eigen(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_eigen))) vm_eigen(m_val); }
};

vm_obj to_obj(Eigen::ArrayXf const & v) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_eigen))) vm_eigen(v));
}

Eigen::ArrayXf to_eigen(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_eigen*>(to_external(o)));
    return static_cast<vm_eigen*>(to_external(o))->m_val;
}

long unsigned shape_len(vm_obj const & shape) {
    list<unsigned> dims = to_list<unsigned>(shape, to_unsigned);
    long unsigned len = 1;
    for (unsigned dim : dims)
        len *= dim;
    return len;
}

vm_obj eigen_zero(vm_obj const & shape) { return to_obj(Eigen::ArrayXd::Zero(shape_len(shape))); }
vm_obj eigen_one(vm_obj const & shape) { return to_obj(Eigen::ArrayXd::Ones(shape_len(shape))); }

// vm_obj eigen_neg(vm_obj const & x) { return to_obj(-to_eigen(x)); }
// vm_obj eigen_inv(vm_obj const & x) { return to_obj(1.0/to_eigen(x)); }
// vm_obj eigen_exp(vm_obj const & x) { return to_obj(exp(to_eigen(x))); }
// vm_obj eigen_log(vm_obj const & x) { return to_obj(log(to_eigen(x))); }

// vm_obj eigen_add(vm_obj const & x, vm_obj const & y) { return to_obj(to_eigen(x) + to_eigen(y)); }
// vm_obj eigen_mul(vm_obj const & x, vm_obj const & y) { return to_obj(to_eigen(x) * to_eigen(y)); }
// vm_obj eigen_sub(vm_obj const & x, vm_obj const & y) { return to_obj(to_eigen(x) - to_eigen(y)); }
// vm_obj eigen_div(vm_obj const & x, vm_obj const & y) { return to_obj(to_eigen(x) / to_eigen(y)); }

vm_obj eigen_to_string(vm_obj const & x) {
    std::ostringstream out;
    out << to_eigen(x);
    return to_obj(out.str());
}

void initialize_vm_eigen() {
    DECLARE_VM_BUILTIN(name({"eigen", "zero"}),       eigen_zero);
    DECLARE_VM_BUILTIN(name({"eigen", "one"}),        eigen_one);
    DECLARE_VM_BUILTIN(name({"eigen", "to_string"}),  eigen_to_string);
}

void finalize_vm_eigen() {}

}
