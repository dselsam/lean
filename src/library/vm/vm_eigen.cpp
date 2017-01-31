/*
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include <iostream>
#include "library/vm/vm.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_float.h"
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

vm_obj eigen_to_string(vm_obj const & shape, vm_obj const & v) {
    list<unsigned> dims = to_list<unsigned, std::function<unsigned(vm_obj const &)> >(shape, to_unsigned);
    if (length(dims) <= 1) {
        std::ostringstream out;
        out << to_eigen(v).transpose();
        return to_obj(out.str());
    } else if (length(dims) == 2) {
        // Print matrices specially
        Eigen::Map<Eigen::MatrixXf> M(to_eigen(v).data(), head(dims), head(tail(dims)));
        std::ostringstream out;
        out << M.transpose();
        return to_obj(out.str());
    } else {
        std::ostringstream out;
        out << dims << to_eigen(v).transpose();
        return to_obj(out.str());
    }
}

static long unsigned shape_len(vm_obj const & shape) {
    list<unsigned> dims = to_list<unsigned, std::function<unsigned(vm_obj const &)> >(shape, to_unsigned);
    long unsigned len = 1;
    for (unsigned dim : dims)
        len *= dim;
    return len;
}

vm_obj eigen_box(vm_obj const & x) {
    Eigen::ArrayXf arr(1);
    arr(0) = to_float(x);
    return to_obj(arr);
}

vm_obj eigen_zero(vm_obj const & shape) { return to_obj(Eigen::ArrayXf::Zero(shape_len(shape))); }
vm_obj eigen_one(vm_obj const & shape) { return to_obj(Eigen::ArrayXf::Ones(shape_len(shape))); }

vm_obj eigen_neg(vm_obj const & /* shape */, vm_obj const & x) { return to_obj(-to_eigen(x)); }
vm_obj eigen_inv(vm_obj const & /* shape */, vm_obj const & x) { return to_obj(1.0/to_eigen(x)); }
vm_obj eigen_exp(vm_obj const & /* shape */, vm_obj const & x) { return to_obj(exp(to_eigen(x))); }
vm_obj eigen_log(vm_obj const & /* shape */, vm_obj const & x) { return to_obj(log(to_eigen(x))); }
vm_obj eigen_sqrt(vm_obj const & /* shape */, vm_obj const & x) { return to_obj(sqrt(to_eigen(x))); }
vm_obj eigen_tanh(vm_obj const & /* shape */, vm_obj const & x) { return to_obj(tanh(to_eigen(x))); }

vm_obj eigen_add(vm_obj const & /* shape */, vm_obj const & x, vm_obj const & y) { return to_obj(to_eigen(x) + to_eigen(y)); }
vm_obj eigen_mul(vm_obj const & /* shape */, vm_obj const & x, vm_obj const & y) { return to_obj(to_eigen(x) * to_eigen(y)); }
vm_obj eigen_sub(vm_obj const & /* shape */, vm_obj const & x, vm_obj const & y) { return to_obj(to_eigen(x) - to_eigen(y)); }
vm_obj eigen_div(vm_obj const & /* shape */, vm_obj const & x, vm_obj const & y) { return to_obj(to_eigen(x) / to_eigen(y)); }

vm_obj eigen_smul(vm_obj const & alpha, vm_obj const & /* shape */, vm_obj const & x) { return to_obj(to_float(alpha) * to_eigen(x)); }

vm_obj eigen_sum(vm_obj const & /* shape */, vm_obj const & x) { return to_obj(to_eigen(x).sum()); }
vm_obj eigen_prod(vm_obj const & /* shape */, vm_obj const & x) { return to_obj(to_eigen(x).prod()); }

vm_obj eigen_get_row(vm_obj const & m, vm_obj const & n, vm_obj const & M, vm_obj const & ridx) {
// meta constant get_row {m n : ℕ} (M : T [m, n]) (ridx : fin m) : T [n]
    Eigen::Map<Eigen::MatrixXf> MM(to_eigen(M).data(), to_unsigned(m), to_unsigned(n));
    Eigen::VectorXf v = MM.row(to_unsigned(cfield(ridx, 0)));
    return to_obj(v.array());
}

vm_obj eigen_get_col(vm_obj const & m, vm_obj const & n, vm_obj const & M, vm_obj const & cidx) {
// meta constant get_col {m n : ℕ} (M : T [m, n]) (cidx : fin n) : T [m]
    Eigen::Map<Eigen::MatrixXf> MM(to_eigen(M).data(), to_unsigned(m), to_unsigned(n));
    Eigen::VectorXf v = MM.col(to_unsigned(cfield(cidx, 0)));
    return to_obj(v.array());
}

// TODO(dhs): better to take a proof that ncols_to_take is sufficiently small
vm_obj eigen_get_col_range(vm_obj const & m, vm_obj const & n, vm_obj const & M, vm_obj const & cidx, vm_obj const & ncols_to_take) {
// meta constant get_col_range {m n : ℕ} (M : T [m, n]) (cidx : fin n) (ncols_to_take : ℕ) : T [m, ncols_to_take]
    Eigen::Map<Eigen::MatrixXf> MM(to_eigen(M).data(), to_unsigned(m), to_unsigned(n));
    Eigen::VectorXf v = MM.block(0, to_unsigned(cfield(cidx, 0)), to_unsigned(m), to_unsigned(ncols_to_take));
    return to_obj(v.array());
}

vm_obj eigen_gemv(vm_obj const & m, vm_obj const & n, vm_obj const & M, vm_obj const & v) {
// meta constant gemv {m n : ℕ} (M : T [m, n]) (x : T [n]) : T [m]
    Eigen::Map<Eigen::MatrixXf> MM(to_eigen(M).data(), to_unsigned(m), to_unsigned(n));
    Eigen::VectorXf vv = MM * to_eigen(v).matrix();
    return to_obj(vv.array());
}

vm_obj eigen_gemm(vm_obj const & m, vm_obj const & n, vm_obj const & p, vm_obj const & M, vm_obj const & N) {
// meta constant gemm {m n p : ℕ} (M : T [m, n]) (N : T [n, p]) : T [m, p]
    Eigen::Map<Eigen::MatrixXf> MM(to_eigen(M).data(), to_unsigned(m), to_unsigned(n));
    Eigen::Map<Eigen::MatrixXf> NN(to_eigen(N).data(), to_unsigned(n), to_unsigned(p));
    Eigen::MatrixXf result = MM * NN;
    Eigen::Map<Eigen::VectorXf> v(result.data(), to_unsigned(m) * to_unsigned(p));
    return to_obj(v.array());
}

void initialize_vm_eigen() {
    DECLARE_VM_BUILTIN(name({"eigen", "to_string"}),        eigen_to_string);
    DECLARE_VM_BUILTIN(name({"eigen", "box"}),              eigen_box);

    DECLARE_VM_BUILTIN(name({"eigen", "zero"}),             eigen_zero);
    DECLARE_VM_BUILTIN(name({"eigen", "one"}),              eigen_one);

    DECLARE_VM_BUILTIN(name({"eigen", "neg"}),              eigen_neg);
    DECLARE_VM_BUILTIN(name({"eigen", "inv"}),              eigen_inv);
    DECLARE_VM_BUILTIN(name({"eigen", "exp"}),              eigen_exp);
    DECLARE_VM_BUILTIN(name({"eigen", "log"}),              eigen_log);
    DECLARE_VM_BUILTIN(name({"eigen", "sqrt"}),             eigen_sqrt);
    DECLARE_VM_BUILTIN(name({"eigen", "tanh"}),             eigen_tanh);

    DECLARE_VM_BUILTIN(name({"eigen", "add"}),              eigen_add);
    DECLARE_VM_BUILTIN(name({"eigen", "mul"}),              eigen_mul);
    DECLARE_VM_BUILTIN(name({"eigen", "sub"}),              eigen_sub);
    DECLARE_VM_BUILTIN(name({"eigen", "div"}),              eigen_div);

    DECLARE_VM_BUILTIN(name({"eigen", "smul"}),             eigen_smul);
    DECLARE_VM_BUILTIN(name({"eigen", "sum"}),              eigen_sum);
    DECLARE_VM_BUILTIN(name({"eigen", "prod"}),             eigen_prod);

    DECLARE_VM_BUILTIN(name({"eigen", "get_row"}),          eigen_get_row);
    DECLARE_VM_BUILTIN(name({"eigen", "get_col"}),          eigen_get_col);
    DECLARE_VM_BUILTIN(name({"eigen", "get_col_range"}),    eigen_get_col_range);

    DECLARE_VM_BUILTIN(name({"eigen", "gemv"}),             eigen_gemv);
    DECLARE_VM_BUILTIN(name({"eigen", "gemm"}),             eigen_gemm);
}

void finalize_vm_eigen() {}

}
