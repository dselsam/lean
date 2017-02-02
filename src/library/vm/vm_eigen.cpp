/*
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include <iostream>
#include <random>
#include "library/vm/vm.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_float.h"
#include "library/vm/vm_eigen.h"

namespace lean {

struct vm_eigen : public vm_external {
    Eigen::ArrayXXf m_val;
    vm_eigen(Eigen::ArrayXXf const & v): m_val(v) {}
    virtual ~vm_eigen() {}
    virtual void dealloc() override { this->~vm_eigen(); get_vm_allocator().deallocate(sizeof(vm_eigen), this); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_eigen(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_eigen))) vm_eigen(m_val); }
};

vm_obj to_obj(Eigen::ArrayXXf const & v) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_eigen))) vm_eigen(v));
}

Eigen::ArrayXXf to_eigen(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_eigen*>(to_external(o)));
    return static_cast<vm_eigen*>(to_external(o))->m_val;
}

static optional<pair<unsigned, unsigned> > is_matrix(vm_obj const & shape) {
    list<unsigned> dims = to_list<unsigned, std::function<unsigned(vm_obj const &)> >(shape, to_unsigned);
    if (length(dims) == 2) {
        return optional<pair<unsigned, unsigned> >(head(dims), head(tail(dims)));
    } else {
        return optional<pair<unsigned, unsigned> >();
    }
}

static vm_obj box(float const & x) {
    Eigen::ArrayXXf arr(1, 1);
    arr(0, 0) = x;
    return to_obj(arr);
}

static float unbox(vm_obj const & alpha) {
    return to_eigen(alpha)(0, 0);
}

vm_obj eigen_real() {
    // TODO(dhs): awkward
    return mk_vm_unit();
}

vm_obj eigen_tensor(vm_obj const & shape) {
    // TODO(dhs): awkward
    return mk_vm_unit();
}

vm_obj eigen_to_string(vm_obj const & shape, vm_obj const & v) {
    list<unsigned> dims = to_list<unsigned, std::function<unsigned(vm_obj const &)> >(shape, to_unsigned);
    std::ostringstream out;
    out << dims << std::endl;
    if (optional<pair<unsigned, unsigned> > mn = is_matrix(shape)) {
        out << to_eigen(v);
    } else {
        out << to_eigen(v).transpose();
    }
    return to_obj(out.str());
}

static long unsigned shape_len(vm_obj const & shape) {
    list<unsigned> dims = to_list<unsigned, std::function<unsigned(vm_obj const &)> >(shape, to_unsigned);
    long unsigned len = 1;
    for (unsigned dim : dims)
        len *= dim;
    return len;
}

vm_obj eigen_box(vm_obj const & x) {
    return box(to_float(x));
}

vm_obj eigen_of_nat(vm_obj const & n) {
    return box(float(to_unsigned(n)));
}

vm_obj eigen_zero(vm_obj const & shape) {
    Eigen::ArrayXXf arr;
    if (optional<pair<unsigned, unsigned> > mn = is_matrix(shape)) {
        return to_obj(Eigen::ArrayXXf::Zero(mn->first, mn->second));
    } else {
        return to_obj(Eigen::ArrayXXf::Zero(shape_len(shape), 1));
    }
}

vm_obj eigen_one(vm_obj const & shape) {
    Eigen::ArrayXXf arr;
    if (optional<pair<unsigned, unsigned> > mn = is_matrix(shape)) {
        return to_obj(Eigen::ArrayXXf::Ones(mn->first, mn->second));
    } else {
        return to_obj(Eigen::ArrayXXf::Ones(shape_len(shape), 1));
    }
}

vm_obj eigen_pi(vm_obj const & shape) {
    Eigen::ArrayXXf arr;
    if (optional<pair<unsigned, unsigned> > mn = is_matrix(shape)) {
        return to_obj(Eigen::ArrayXXf::NullaryExpr(mn->first, mn->second, [&]() {
                    return 3.14159265358979323846;
                }));
    } else {
        return to_obj(Eigen::ArrayXXf::NullaryExpr(shape_len(shape), 1, [&]() {
                    return 3.14159265358979323846;
                }));
    }
}

vm_obj eigen_const(vm_obj const & alpha, vm_obj const & shape) {
    Eigen::ArrayXXf arr;
    if (optional<pair<unsigned, unsigned> > mn = is_matrix(shape)) {
        return to_obj(Eigen::ArrayXXf::NullaryExpr(mn->first, mn->second, [&]() {
                    return unbox(alpha);
                }));
    } else {
        return to_obj(Eigen::ArrayXXf::NullaryExpr(shape_len(shape), 1, [&]() {
                    return unbox(alpha);
                }));
    }
}

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

vm_obj eigen_smul(vm_obj const & alpha, vm_obj const & /* shape */, vm_obj const & x) {
    return to_obj(to_eigen(alpha)(0, 0) * to_eigen(x));
}

vm_obj eigen_sum(vm_obj const & /* shape */, vm_obj const & x) { return box(to_eigen(x).sum()); }
vm_obj eigen_prod(vm_obj const & /* shape */, vm_obj const & x) { return box(to_eigen(x).prod()); }

vm_obj eigen_get_row(vm_obj const & m, vm_obj const & n, vm_obj const & M, vm_obj const & ridx) {
// meta constant get_row {m n : ℕ} (M : T [m, n]) (ridx : fin m) : T [n]
    return to_obj(to_eigen(M).matrix().row(to_unsigned(ridx)).transpose().array());
}

vm_obj eigen_get_col(vm_obj const & m, vm_obj const & n, vm_obj const & M, vm_obj const & cidx) {
// meta constant get_col {m n : ℕ} (M : T [m, n]) (cidx : fin n) : T [m]
    return to_obj(to_eigen(M).matrix().col(to_unsigned(cidx)).array());
}

// TODO(dhs): better to take a proof that ncols_to_take is sufficiently small
vm_obj eigen_get_col_range(vm_obj const & m, vm_obj const & n, vm_obj const & M, vm_obj const & cidx, vm_obj const & ncols_to_take) {
// meta constant get_col_range {m n : ℕ} (M : T [m, n]) (cidx : fin n) (ncols_to_take : ℕ) : T [m, ncols_to_take]
    return to_obj(to_eigen(M).block(0, to_unsigned(cidx), to_unsigned(m), to_unsigned(ncols_to_take)).array());
}

vm_obj eigen_gemv(vm_obj const & m, vm_obj const & n, vm_obj const & M, vm_obj const & v) {
// meta constant gemv {m n : ℕ} (M : T [m, n]) (x : T [n]) : T [m]
    Eigen::VectorXf result = to_eigen(M).matrix() * to_eigen(v).matrix();
    return to_obj(result.array());
}

vm_obj eigen_gemm(vm_obj const & m, vm_obj const & n, vm_obj const & p, vm_obj const & M, vm_obj const & N) {
// meta constant gemm {m n p : ℕ} (M : T [m, n]) (N : T [n, p]) : T [m, p]
    Eigen::MatrixXf result = to_eigen(M).matrix() * to_eigen(N).matrix();
    return to_obj(result.array());
}

// Random

struct vm_rng : public vm_external {
    std::minstd_rand m_val;
    vm_rng(std::minstd_rand const & rng): m_val(rng) {}
    virtual ~vm_rng() {}
    virtual void dealloc() override { this->~vm_rng(); get_vm_allocator().deallocate(sizeof(vm_rng), this); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_rng(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_rng))) vm_rng(m_val); }
};

vm_obj to_obj(std::minstd_rand const & rng) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_rng))) vm_rng(rng));
}

std::minstd_rand const & to_rng(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_rng*>(to_external(o)));
    return static_cast<vm_rng*>(to_external(o))->m_val;
}

vm_obj eigen_rng_to_string(vm_obj const & rng) {
    std::ostringstream out;
    out << to_rng(rng);
    return to_obj(out.str());
}

vm_obj eigen_mk_rng(vm_obj const & seed) {
    // TODO(dhs): take a proof that it is small enough
    return to_obj(std::minstd_rand(to_unsigned(seed)));
}

static float sample_gauss(float mu, float sigma, std::minstd_rand & g) {
    std::normal_distribution<float> dist(mu, sigma);
    float x = dist(g);
    std::cout << "sample_gauss: " << x << std::endl;
    return x;
}

vm_obj eigen_sample_gauss(vm_obj const & shape, vm_obj const & mu, vm_obj const & sigma, vm_obj const & g_old) {
    std::cout << "[sample_gauss]" << std::endl;
    std::minstd_rand g = to_rng(g_old);
    if (optional<pair<unsigned, unsigned> > mn = is_matrix(shape)) {
        Eigen::ArrayXXf arr = Eigen::ArrayXXf::NullaryExpr(mn->first, mn->second, [&]() { return sample_gauss(unbox(mu), unbox(sigma), g); });
        std::cout << "matrix" << arr << std::endl;
        return mk_vm_pair(to_obj(arr), to_obj(g));
    } else {
        Eigen::ArrayXXf arr = Eigen::ArrayXXf::NullaryExpr(shape_len(shape), 1, [&]() { return sample_gauss(unbox(mu), unbox(sigma), g); });
        std::cout << "non-matrix" << to_eigen(to_obj(arr)) << std::endl;
        return mk_vm_pair(to_obj(arr), to_obj(g));
    }
}

static float sample_uniform(float low, float high, std::minstd_rand & g) {
    std::uniform_real_distribution<float> dist(low, high);
    float x = dist(g);
    std::cout << "sample_uniform: " << x << std::endl;
    return x;
}

vm_obj eigen_sample_uniform(vm_obj const & shape, vm_obj const & low, vm_obj const & high, vm_obj const & g_old) {
    std::cout << "[sample_uniform]" << std::endl;
    std::minstd_rand g = to_rng(g_old);
    if (optional<pair<unsigned, unsigned> > mn = is_matrix(shape)) {
        Eigen::ArrayXXf arr = Eigen::ArrayXXf::NullaryExpr(mn->first, mn->second, [&]() { return sample_uniform(unbox(low), unbox(high), g); });
        std::cout << "matrix" << arr << std::endl;
        return mk_vm_pair(to_obj(arr), to_obj(g));
    } else {
        Eigen::ArrayXXf arr = Eigen::ArrayXXf::NullaryExpr(shape_len(shape), 1, [&]() { return sample_uniform(unbox(low), unbox(high), g); });
        std::cout << "non-matrix" << to_eigen(to_obj(arr)) << std::endl;
        return mk_vm_pair(to_obj(arr), to_obj(g));
    }
}

void initialize_vm_eigen() {
    DECLARE_VM_BUILTIN(name({"certigrad", "RNG", "to_string"}),      eigen_rng_to_string);
    DECLARE_VM_BUILTIN(name({"certigrad", "RNG", "mk"}),             eigen_mk_rng);

    DECLARE_VM_BUILTIN(name({"certigrad", "R"}),                     eigen_real);
    DECLARE_VM_BUILTIN(name({"certigrad", "T"}),                     eigen_tensor);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "to_string"}),        eigen_to_string);

    DECLARE_VM_BUILTIN(name({"certigrad", "T", "of_nat"}),           eigen_of_nat);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "box"}),              eigen_box);

    DECLARE_VM_BUILTIN(name({"certigrad", "T", "zero"}),             eigen_zero);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "one"}),              eigen_one);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "pi"}),               eigen_pi);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "const"}),            eigen_const);

    DECLARE_VM_BUILTIN(name({"certigrad", "T", "neg"}),              eigen_neg);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "inv"}),              eigen_inv);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "exp"}),              eigen_exp);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "log"}),              eigen_log);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "sqrt"}),             eigen_sqrt);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "tanh"}),             eigen_tanh);

    DECLARE_VM_BUILTIN(name({"certigrad", "T", "add"}),              eigen_add);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "mul"}),              eigen_mul);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "sub"}),              eigen_sub);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "div"}),              eigen_div);

    DECLARE_VM_BUILTIN(name({"certigrad", "T", "smul"}),             eigen_smul);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "sum"}),              eigen_sum);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "prod"}),             eigen_prod);

    DECLARE_VM_BUILTIN(name({"certigrad", "T", "get_row"}),          eigen_get_row);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "get_col"}),          eigen_get_col);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "get_col_range"}),    eigen_get_col_range);

    DECLARE_VM_BUILTIN(name({"certigrad", "T", "gemv"}),             eigen_gemv);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "gemm"}),             eigen_gemm);

    DECLARE_VM_BUILTIN(name({"certigrad", "T", "sample_uniform"}),   eigen_sample_uniform);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "sample_gauss"}),     eigen_sample_gauss);
}

void finalize_vm_eigen() {}

}
