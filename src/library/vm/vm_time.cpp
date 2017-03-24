/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include <time.h>
#include <string>
#include "library/vm/vm.h"
#include "library/vm/vm_io.h"
#include "library/vm/vm_string.h"

namespace lean {

struct vm_time_t : public vm_external {
    time_t m_val;
    vm_time_t(time_t const & val): m_val(val) {}
    virtual ~vm_time_t() {}
    virtual void dealloc() override { this->~vm_time_t(); get_vm_allocator().deallocate(sizeof(vm_time_t), this); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_time_t(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_time_t))) vm_time_t(m_val); }
};

vm_obj to_obj(time_t const & val) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_time_t))) vm_time_t(val));
}

time_t const & to_time_t(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_time_t*>(to_external(o)));
    return static_cast<vm_time_t*>(to_external(o))->m_val;
}

vm_obj vm_time_sdiff(vm_obj const & t1, vm_obj const & t2) {
    double seconds = difftime(to_time_t(t1), to_time_t(t2));
    std::ostringstream out;
    out << seconds;
    return to_obj(out.str());
}

vm_obj io_get_time(vm_obj const &, vm_obj const &) {
    time_t t = time(NULL);
    return mk_io_result(to_obj(t));
}

void initialize_vm_time() {
    DECLARE_VM_BUILTIN(name({"time", "get"}), io_get_time);
    DECLARE_VM_BUILTIN(name({"time", "sdiff"}), vm_time_sdiff);
}

void finalize_vm_time() {
}
}
