/*
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include <sys/types.h>
#include <sys/stat.h>
#include <iostream>
#include <fstream>
#include <random>
#include "util/sstream.h"
#include "library/vm/vm.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_io.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_eigen.h"

namespace lean {

static const float eps = 0.00000001;

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

Eigen::ArrayXXf const & to_eigen(vm_obj const & o) {
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

vm_obj eigen_dummy() {
    // TODO(dhs): awkward
    throw exception("eigen_dummy not supposed to be called");
    return mk_vm_unit();
}

vm_obj eigen_to_string(vm_obj const & shape, vm_obj const & v) {
    list<unsigned> dims = to_list<unsigned, std::function<unsigned(vm_obj const &)> >(shape, to_unsigned);
    std::ostringstream out;
    if (optional<pair<unsigned, unsigned> > mn = is_matrix(shape)) {
        out << dims << std::endl << to_eigen(v);
    } else if (is_nil(dims)) {
        out << unbox(v);
    } else {
        out << dims << std::endl << to_eigen(v).transpose();
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

vm_obj eigen_of_nat(vm_obj const & n) {
    return box(float(to_unsigned(n)));
}

vm_obj eigen_round(vm_obj const & x) {
    return mk_vm_nat(static_cast<unsigned>(round(unbox(x))));
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
vm_obj eigen_inv(vm_obj const & /* shape */, vm_obj const & x) {
    Eigen::ArrayXXf arr = 1.0 / (to_eigen(x));
    if (!arr.allFinite())
        throw exception("inv floating point error");
    return to_obj(arr);
}
vm_obj eigen_exp(vm_obj const & /* shape */, vm_obj const & x) { return to_obj(exp(to_eigen(x))); }
vm_obj eigen_log(vm_obj const & /* shape */, vm_obj const & x) {
    Eigen::ArrayXXf arr = log(to_eigen(x) + eps);
    if (!arr.allFinite())
        throw exception("log floating point error");
    return to_obj(arr);
}

vm_obj eigen_sqrt(vm_obj const & /* shape */, vm_obj const & x) { return to_obj(sqrt(to_eigen(x))); }
vm_obj eigen_tanh(vm_obj const & /* shape */, vm_obj const & x) { return to_obj(tanh(to_eigen(x))); }

vm_obj eigen_pow(vm_obj const & /* shape */, vm_obj const & x, vm_obj const & alpha) { return to_obj(to_eigen(x).pow(unbox(alpha))); }

vm_obj eigen_add(vm_obj const & /* shape */, vm_obj const & x, vm_obj const & y) { return to_obj(to_eigen(x) + to_eigen(y)); }
vm_obj eigen_mul(vm_obj const & /* shape */, vm_obj const & x, vm_obj const & y) { return to_obj(to_eigen(x) * to_eigen(y)); }
vm_obj eigen_sub(vm_obj const & /* shape */, vm_obj const & x, vm_obj const & y) { return to_obj(to_eigen(x) - to_eigen(y)); }
vm_obj eigen_div(vm_obj const & /* shape */, vm_obj const & x, vm_obj const & y) {
    // TODO(dhs): denom might be neg
    Eigen::ArrayXXf arr = to_eigen(x) / (to_eigen(y) + eps);
    if (!arr.allFinite())
        throw exception("div floating point error");
    return to_obj(arr);
}

vm_obj eigen_transpose(vm_obj const & /* m */, vm_obj const & /* n */, vm_obj const & M) {
    return to_obj(to_eigen(M).transpose());
}

vm_obj eigen_smul(vm_obj const & /* shape */, vm_obj const & alpha, vm_obj const & x) {
    return to_obj(unbox(alpha) * to_eigen(x));
}

vm_obj eigen_sum(vm_obj const & /* shape */, vm_obj const & x) { return box(to_eigen(x).sum()); }
vm_obj eigen_prod(vm_obj const & /* shape */, vm_obj const & x) { return box(to_eigen(x).prod()); }

vm_obj eigen_get_row(vm_obj const & /* m */, vm_obj const & /* n */, vm_obj const & M, vm_obj const & ridx) {
// meta constant get_row {m n : ℕ} (M : T [m, n]) (ridx : fin m) : T [n]
    return to_obj(to_eigen(M).matrix().row(to_unsigned(ridx)).transpose().array());
}

vm_obj eigen_get_col(vm_obj const & /* m */, vm_obj const & /* n */, vm_obj const & M, vm_obj const & cidx) {
// meta constant get_col {m n : ℕ} (M : T [m, n]) (cidx : fin n) : T [m]
    return to_obj(to_eigen(M).matrix().col(to_unsigned(cidx)).array());
}

vm_obj eigen_get_col_range(vm_obj const & m, vm_obj const & /* n */, vm_obj const & ncols_to_take, vm_obj const & M, vm_obj const & cidx) {
    return to_obj(to_eigen(M).block(0, to_unsigned(cidx), to_unsigned(m), to_unsigned(ncols_to_take)).array());
}

vm_obj eigen_sum_cols(vm_obj const & /* m */, vm_obj const & /* n */, vm_obj const & M) {
// def sum_cols {nrows ncols : ℕ} (M : T [nrows, ncols]) : T [nrows] :=
    return to_obj(to_eigen(M).matrix().rowwise().sum().array());
}

vm_obj eigen_replicate_col(vm_obj const & /* m */, vm_obj const & v, vm_obj const & n) {
// def replicate_col {m : ℕ} (v : T [m]) (n : ℕ) : T [m, n] :=
    return to_obj(to_eigen(v).replicate(1, to_unsigned(n)));
}

vm_obj eigen_gemv(vm_obj const & /* m */, vm_obj const & /* n */, vm_obj const & M, vm_obj const & v) {
// meta constant gemv {m n : ℕ} (M : T [m, n]) (x : T [n]) : T [m]
    Eigen::VectorXf result = to_eigen(M).matrix() * to_eigen(v).matrix();
    return to_obj(result.array());
}

vm_obj eigen_gemm(vm_obj const & /* m */, vm_obj const & /* n */, vm_obj const & /* p */, vm_obj const & M, vm_obj const & N) {
// meta constant gemm {m n p : ℕ} (M : T [m, n]) (N : T [n, p]) : T [m, p]
    Eigen::MatrixXf result = to_eigen(M).matrix() * to_eigen(N).matrix();
    return to_obj(result.array());
}

vm_obj eigen_read_from_file(vm_obj const & shape, vm_obj const & _filename, vm_obj const &, vm_obj const &) {
    std::string filename = to_string(_filename);
    std::ifstream in(filename);

    unsigned nrows, ncols;
    if (optional<pair<unsigned, unsigned> > mn = is_matrix(shape)) {
        nrows = mn->first;
        ncols = mn->second;
    } else {
        nrows = shape_len(shape);
        ncols = 1;
    }
    Eigen::ArrayXXf arr(nrows, ncols);

    for (unsigned row = 0; row < nrows; row++) {
        for (unsigned col = 0; col < ncols; col++) {
            in >> arr(row, col);
        }
    }
    return mk_io_result(to_obj(arr));
}

vm_obj eigen_write_to_file(vm_obj const & /* shape */, vm_obj const & x, vm_obj const & _filename, vm_obj const &, vm_obj const &) {
    std::string filename = to_string(_filename);
    std::ofstream out(filename);

    out.precision(18);
    out << std::scientific;
    Eigen::ArrayXXf arr = to_eigen(x);
    for (unsigned row = 0; row < arr.rows(); row++) {
        for (unsigned col = 0; col < arr.cols(); col++) {
            out << arr(row, col) << " ";
        }
        out << "\n";
    }
    return mk_io_result(mk_vm_unit());
}

vm_obj eigen_fail(vm_obj const & shape) {
    list<unsigned> dims = to_list<unsigned, std::function<unsigned(vm_obj const &)> >(shape, to_unsigned);
    throw exception(sstream() << "certigrad.T.fail default tensor value returned of shape "<< dims << "\n");
}

vm_obj eigen_silent_fail(vm_obj const & /* shape */) {
    Eigen::MatrixXf empty;
    return to_obj(empty);
}

vm_obj eigen_error(vm_obj const & /* shape */, vm_obj const & msg) {
    throw exception(sstream() << "certigrad.T.error: " << to_string(msg) << "\n");
}

vm_obj eigen_le(vm_obj const & /* shape */, vm_obj const & /* x */, vm_obj const & /* y */) {
    throw exception("eigen_le not expected to be called");
}
vm_obj eigen_lt(vm_obj const & /* shape */, vm_obj const & /* x */, vm_obj const & /* y */) {
    throw exception("eigen_lt not expected to be called");
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
    return to_obj(std::minstd_rand(to_unsigned(seed)));
}

static float sample_mvn_iso(float mu, float sigma, std::minstd_rand & g) {
    std::normal_distribution<float> dist(mu, sigma);
    float x = dist(g);
    return x;
}

vm_obj eigen_sample_mvn_iso(vm_obj const & /* shape */, vm_obj const & _mu, vm_obj const & _sigma, vm_obj const & g_old) {
    std::minstd_rand g = to_rng(g_old);
    Eigen::ArrayXXf mus = to_eigen(_mu);
    Eigen::ArrayXXf sigmas = to_eigen(_sigma);

    Eigen::ArrayXXf arr = mus.binaryExpr(sigmas, [&](float const & mu, float const & sigma) {
            return sample_mvn_iso(mu, sigma, g);
        });
    return mk_vm_pair(to_obj(arr), to_obj(g));
}

static float sample_uniform(float low, float high, std::minstd_rand & g) {
    std::uniform_real_distribution<float> dist(low, high);
    float x = dist(g);
    return x;
}

vm_obj eigen_sample_uniform(vm_obj const & shape, vm_obj const & low, vm_obj const & high, vm_obj const & g_old) {
    std::minstd_rand g = to_rng(g_old);
    float x_low = unbox(low);
    float x_high = unbox(high);
    if (optional<pair<unsigned, unsigned> > mn = is_matrix(shape)) {
        Eigen::ArrayXXf arr = Eigen::ArrayXXf::NullaryExpr(mn->first, mn->second, [&]() { return sample_uniform(x_low, x_high, g); });
        return mk_vm_pair(to_obj(arr), to_obj(g));
    } else {
        Eigen::ArrayXXf arr = Eigen::ArrayXXf::NullaryExpr(shape_len(shape), 1, [&]() { return sample_uniform(x_low, x_high, g); });
        return mk_vm_pair(to_obj(arr), to_obj(g));
    }
}

vm_obj io_mkdir(vm_obj const & dir_name, vm_obj const &, vm_obj const &) {
    int status = mkdir(to_string(dir_name).c_str(), S_IRWXU);
    return mk_io_result(mk_vm_nat(status));
}

void initialize_vm_eigen() {
    Eigen::initParallel();
    Eigen::setNbThreads(2);

    DECLARE_VM_BUILTIN(name({"certigrad", "RNG"}),                   eigen_dummy);
    DECLARE_VM_BUILTIN(name({"certigrad", "T"}),                     eigen_dummy);

    DECLARE_VM_BUILTIN(name({"certigrad", "RNG", "to_string"}),      eigen_rng_to_string);
    DECLARE_VM_BUILTIN(name({"certigrad", "RNG", "mk"}),             eigen_mk_rng);

    DECLARE_VM_BUILTIN(name({"certigrad", "T", "to_string"}),        eigen_to_string);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "fail"}),             eigen_fail);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "silent_fail"}),      eigen_silent_fail);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "error"}),            eigen_error);

    DECLARE_VM_BUILTIN(name({"certigrad", "T", "of_nat"}),           eigen_of_nat);

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
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "pow"}),              eigen_pow);

    DECLARE_VM_BUILTIN(name({"certigrad", "T", "add"}),              eigen_add);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "mul"}),              eigen_mul);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "sub"}),              eigen_sub);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "div"}),              eigen_div);

    DECLARE_VM_BUILTIN(name({"certigrad", "T", "round"}),            eigen_round);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "transpose"}),        eigen_transpose);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "scalar_mul"}),       eigen_smul);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "sum"}),              eigen_sum);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "prod"}),             eigen_prod);

    DECLARE_VM_BUILTIN(name({"certigrad", "T", "get_row"}),          eigen_get_row);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "get_col"}),          eigen_get_col);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "get_col_range"}),    eigen_get_col_range);

    DECLARE_VM_BUILTIN(name({"certigrad", "T", "sum_cols"}),         eigen_sum_cols);

    DECLARE_VM_BUILTIN(name({"certigrad", "T", "replicate_col"}),    eigen_replicate_col);

    DECLARE_VM_BUILTIN(name({"certigrad", "T", "gemv"}),             eigen_gemv);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "gemm"}),             eigen_gemm);

    DECLARE_VM_BUILTIN(name({"certigrad", "T", "le"}),               eigen_le);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "lt"}),               eigen_lt);

    DECLARE_VM_BUILTIN(name({"certigrad", "T", "read_from_file"}),   eigen_read_from_file);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "write_to_file"}),    eigen_write_to_file);

    DECLARE_VM_BUILTIN(name({"certigrad", "T", "sample_uniform"}),   eigen_sample_uniform);
    DECLARE_VM_BUILTIN(name({"certigrad", "T", "sample_mvn_iso"}),   eigen_sample_mvn_iso);

    DECLARE_VM_BUILTIN(name({"io", "mkdir"}),                        io_mkdir);
}

void finalize_vm_eigen() {}

}
