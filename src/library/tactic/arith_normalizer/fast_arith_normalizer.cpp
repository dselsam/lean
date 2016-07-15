/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include <functional>
#include <string>
#include <algorithm>
#include "util/optional.h"
#include "util/timeit.h"
#include "util/interrupt.h"
#include "util/name_hash_map.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/abstract.h"
#include "kernel/expr_maps.h"
#include "kernel/expr_sets.h"
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/expr_lt.h"
#include "library/num.h"
#include "library/util.h"
#include "library/norm_num.h"
#include "library/app_builder.h"
#include "library/fun_info.h"
#include "library/sorry.h"
#include "library/mpq_macro.h"
#include "library/kernel_serializer.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/arith_normalizer/util.h"
#include "library/tactic/arith_normalizer/fast_arith_normalizer.h"

namespace lean {

class fast_arith_normalize_fn {
    type_context &            m_tctx;
    arith_normalize_options   m_options;
    arith_instance_manager *  m_im;

public:
    fast_arith_normalize_fn(type_context & tctx, arith_normalize_options const & options): m_tctx(tctx), m_options(options) {}

    expr operator()(expr const & e) {
        // TODO(dhs): not sure what to do here yet, not sure when the arith_normalizer will be called
        scope_trace_env scope(env(), m_tctx);
        buffer<expr> args;
        expr op = get_app_args(e, args);

        arith_instance_manager inst_manager;

        switch (get_head_type(op)) {
        case head_type::OTHER:
            // TODO(dhs): we may still do something here
            throw exception(sstream() << "fast_arith_normalizer not expecting to be called on expr " << e << "\n");
            return e;
        case head_type::REAL_OF_RAT:
            inst_manager = get_arith_instance_manager_for_real();
            break;
        case head_type::RAT_OF_INT:
            inst_manager = get_arith_instance_manager_for_rat();
            break;
        case head_type::INT_OF_NAT:
            inst_manager = get_arith_instance_manager_for_int();
            break;
        default:
            expr type = args[0];
            arith_instance_manager = get_arith_instance_manager_for(m_tctx, type);
            if (!m_im->is_comm_semiring()) {
                throw exception(sstream() << "fast_arith_normalizer not expecting to be called on expr " << e << " that is not of a type with commutative semiring structure\n");
            }
            break;
        }

        flet<arith_instance_manager *> with_instance_manager(m_im, &inst_manager);

        if (m_options.m_profile) {
            std::ostringstream msg;
            msg << "arith_normalizer time: ";
            timeit timer(get_dummy_ios().get_diagnostic_stream(), msg.str().c_str(), 0.0);
            return fast_normalize(e);
        } else {
            return fast_normalize(e);
        }
    }

private:
    environment env() const { return m_tctx.env(); }

    expr get_current_type() const { return m_im->get_type(); }
    bool current_type_is_nat() const { return m_im->get_type() == mk_constant(get_nat_name()); }
    bool current_type_is_int() const { return m_im->get_type() == mk_constant(get_int_name()); }
    bool current_type_is_rat() const { return m_im->get_type() == mk_constant(get_rat_name()); }
    bool current_type_is_field() const { return m_im->get_type() == mk_constant(get_field_name()); }

    expr fast_normalize(expr const & e, bool process_summands = true, bool process_multiplicands = true) {
        check_system("arith_normalizer");
        lean_trace_inc_depth(name({"arith_normalizer", "fast"}));
        lean_trace_d(name({"arith_normalizer", "fast"}), tout() << e << "\n";);

        buffer<expr> args;
        expr op = get_app_args(e, args);

        unsigned num_args = args.size();
        switch (get_head_type(op)) {
        case head_type::EQ: return fast_normalize_eq(args[1], args[2]);

        case head_type::LE: return fast_normalize_le(args[2], args[3]);
        case head_type::GE: return fast_normalize_ge(args[2], args[3]);

        case head_type::LT: return fast_normalize_lt(args[2], args[3]);
        case head_type::GT: return fast_normalize_gt(args[2], args[3]);

        case head_type::ADD: return fast_normalize_add(e, process_summands, true /* normalize_children */);
        case head_type::MUL: return fast_normalize_mul(e);

        case head_type::SUB: return fast_normalize_sub(args[2], args[3], process_summands);
        case head_type::DIV: return fast_normalize_div(args[2], args[3]);

        case head_type::NEG: return fast_normalize_neg(args[2], process_multiplicands);

        case head_type::INT_OF_NAT: return fast_normalize_int_of_nat(args[0]);
        case head_type::RAT_OF_INT: return fast_normalize_rat_of_int(args[0]);
        case head_type::REAL_OF_RAT: return fast_normalize_real_of_rat(args[0]);

        case head_type::ZERO: case head_type::ONE: case head_type::BIT0: case head_type::BIT1:
            if (auto n = to_num(e))
                return mk_mod_mpq_macro(*m_im, mpq(*n));
            else
                break;

        case head_type::OTHER:
            break;
        }
        // TODO(dhs): this will be unreachable eventually
        return e;
    }

    expr fast_normalize_eq(expr const & lhs, expr const & rhs) { return fast_normalize_rel(lhs, rhs, rel_kind::EQ); }
    expr fast_normalize_le(expr const & lhs, expr const & rhs) { return fast_normalize_rel(lhs, rhs, rel_kind::LE); }
    expr fast_normalize_ge(expr const & lhs, expr const & rhs) { return fast_normalize_rel(rhs, lhs, rel_kind::LE); }
    expr fast_normalize_lt(expr const & lhs, expr const & rhs) {
        expr e = fast_normalize_rel(lhs, rhs, rel_kind::LT);
        buffer<expr> args;
        switch (get_head_type(get_app_args(e, args))) {
        case head_type::LT:
            return mk_app(mk_constant(get_not_name()), mk_app(m_im->get_le(), args[3], args[2]));
        default:
            lean_assert(is_true(e) || is_false(e));
            return e;
        }
    }

    expr fast_normalize_gt(expr const & lhs, expr const & rhs) {
        expr e = fast_normalize_rel(rhs, lhs, rel_kind::LT);
        buffer<expr> args;
        switch (get_head_type(get_app_args(e, args))) {
        case head_type::LT:
            return mk_app(mk_constant(get_not_name()), mk_app(m_im->get_le(), args[3], args[2]));
        default:
            lean_assert(is_true(e) || is_false(e));
            return e;
        }
    }

    expr fast_normalize_rel(expr const & lhs, expr const & rhs, rel_kind rk) {
        bool cancel_monomials = false;
        switch (rk) {
        case rel_kind::EQ:
            cancel_monomials = true;
            break;
        case rel_kind::LE: case rel_kind::LT:
            cancel_monomials = m_im->is_linear_ordered_semiring() && m_im->is_comm_semiring();
            break;
        }

        expr new_lhs, new_rhs;
        if (cancel_monomials) {
            fast_cancel_monomials(lhs, rhs, new_lhs, new_rhs);
        } else {
            new_lhs = fast_normalize(lhs);
            new_rhs = fast_normalize(rhs);
        }

        // TODO(dhs): bounds
        // TODO(dhs): gcd stuff
        // TODO(dhs): clear denominators?

        mpq q1, q2;
        if (is_mpq_macro(new_lhs, q1) && is_mpq_macro(new_rhs, q2)) {
            // TODO(dhs): can we do this reduction without the relations being decidable in general?
            switch (rk) {
            case rel_kind::EQ: return (q1 == q2) ? mk_constant(get_true_name()) : mk_constant(get_false_name());
            case rel_kind::LE: return (q1 <= q2) ? mk_constant(get_true_name()) : mk_constant(get_false_name());
            case rel_kind::LT: return (q1 < q2) ? mk_constant(get_true_name()) : mk_constant(get_false_name());
            }
        } else {
            switch (rk) {
            case rel_kind::EQ: return mk_app(m_im->get_eq(), new_lhs, new_rhs);
            case rel_kind::LE: return mk_app(m_im->get_le(), new_lhs, new_rhs);
            case rel_kind::LT: return mk_app(m_im->get_lt(), new_lhs, new_rhs);
            }
        }
        lean_unreachable();
    }

    // Coercions
    expr fast_normalize_real_of_rat(expr const & e) {
        lean_assert(get_current_type() == mk_constant(get_real_name()));
        expr e_n;
        {
            arith_instance_manager rat_im(m_tctx, mk_constant(get_rat_name()), mk_level_one());
            flet<arith_instance_manager *> use_rat_im(m_im, &rat_im);
            e_n = fast_normalize(e);
        }
        lean_assert(get_current_type() == mk_constant(get_real_name()));
        return fast_push_coe(mk_constant(get_real_of_rat_name()), e_n);
    }

    expr fast_normalize_rat_of_int(expr const & e) {
        lean_assert(get_current_type() == mk_constant(get_rat_name()));
        expr e_n;
        {
            arith_instance_manager int_im(m_tctx, mk_constant(get_int_name()), mk_level_one());
            flet<arith_instance_manager *> use_int_im(m_im, &int_im);
            e_n = fast_normalize(e);
        }
        lean_assert(get_current_type() == mk_constant(get_rat_name()));
        return fast_push_coe(mk_constant(get_rat_of_int_name()), e_n);
    }

    expr fast_normalize_int_of_nat(expr const & e) {
        lean_assert(get_current_type() == mk_constant(get_int_name()));
        expr e_n;
        {
            arith_instance_manager nat_im(m_tctx, mk_constant(get_nat_name()), mk_level_one());
            flet<arith_instance_manager *> use_nat_im(m_im, &nat_im);
            e_n = fast_normalize(e);
        }
        lean_assert(get_current_type() == mk_constant(get_int_name()));
        return fast_push_coe(mk_constant(get_int_of_nat_name()), e_n);
    }

    expr fast_push_coe(expr const & coe, expr const & e) {
        mpq q;
        expr arg1, arg2;

        if (is_mpq_macro(e, q)) {
            return mk_mod_mpq_macro(*m_im, q);
        } else if (is_add(e, arg1, arg2)) {
            lean_assert(!is_add(arg1));
            arg1 = fast_push_coe(coe, arg1);
            arg2 = fast_push_coe(coe, arg2);
            return mk_app(m_im->get_add(), arg1, arg2);
        } else if (is_mul(e, arg1, arg2)) {
            lean_assert(!is_mul(arg1));
            arg1 = fast_push_coe(coe, arg1);
            arg2 = fast_push_coe(coe, arg2);
            return mk_app(m_im->get_mul(), arg1, arg2);
        } else {
            return mk_app(coe, e);
        }
    }

    expr fast_normalize_nat_sub(expr const & e1, expr const & e2) {
        expr arg1, arg2;
        if (is_sub(e1, arg1, arg2)) {
            // Rule 1: sub(sub(arg1, arg2), p) ==> sub(arg1, add(arg2, p))
            bool process_summands = false;
            bool normalize_children = false;
            expr t = mk_app(m_im->get_add(), arg2, e2);
            return fast_normalize_nat_sub(arg1, fast_normalize_add(t, process_summands, normalize_children));
        } else {
            // Rule 2: sub(add(...), add(...)) cancels things that appear in both sides
            // Note: if add is not the head of either argument, it is considered an addition of a single term
            buffer<expr> lhs_monomials, rhs_monomials;
            bool normalize_children = false;

            fast_get_flattened_nary_summands(e1, lhs_monomials, normalize_children);
            fast_get_flattened_nary_summands(e2, rhs_monomials, normalize_children);

            buffer<expr> new_lhs_monomials, new_rhs_monomials;
            mpq coeff;
            bool orient_polys = false;

            fast_cancel_monomials_core(lhs_monomials, rhs_monomials, new_lhs_monomials, new_rhs_monomials, coeff, orient_polys);

            if (new_lhs_monomials.empty() && !coeff.is_pos()) {
                // 0 - x ==> 0
                return m_im->get_zero();
            } else if (new_rhs_monomials.empty() && !coeff.is_neg()) {
                // x - 0 ==> x
                return mk_polynomial(*m_im, coeff, new_lhs_monomials);
            } else if (coeff.is_zero()) {
                return mk_app(m_im->get_sub(), mk_polynomial(*m_im, new_lhs_monomials), mk_polynomial(*m_im, new_rhs_monomials));
            } else if (coeff.is_neg()) {
                coeff.neg();
                return mk_app(m_im->get_sub(), mk_polynomial(*m_im, new_lhs_monomials), mk_polynomial(*m_im, coeff, new_rhs_monomials));
            } else {
                lean_assert(coeff.is_pos());
                return mk_app(m_im->get_sub(), mk_polynomial(*m_im, coeff, new_lhs_monomials), mk_polynomial(*m_im, new_rhs_monomials));
            }
        }
    }

    expr fast_normalize_sub(expr const & e1, expr const & e2, bool process_summands) {
        if (current_type_is_nat()) {
            expr e1_n = fast_normalize(e1);
            expr e2_n = fast_normalize(e2);
            return fast_normalize_nat_sub(e1_n, e2_n);
        } else if (!m_im->is_add_group()) {
            expr e1_n = fast_normalize(e1);
            expr e2_n = fast_normalize(e2);
            return mk_app(m_im->get_sub(), e1_n, e2_n);
        } else if (!process_summands) {
            expr e1_n = fast_normalize(e1);
            expr e2_neg_n = fast_normalize(mk_app(m_im->get_neg(), e2));
            return mk_app(m_im->get_add(), e1_n, e2_neg_n);
        } else {
            expr e2_neg = mk_app(m_im->get_neg(), e2);
            return fast_normalize(mk_app(m_im->get_add(), e1, e2_neg));
        }
    }

    expr fast_normalize_neg(expr const & e, bool process_multiplicands) {
        mpq q(-1);
        expr c = mk_mod_mpq_macro(*m_im, q);
        if (!process_multiplicands) {
            expr e_n = fast_normalize(e);
            return mk_app(m_im->get_mul(), c, e_n);
        } else {
            return fast_normalize(mk_app(m_im->get_mul(), c, e));
        }
    }

    expr fast_normalize_div(expr const & _e1, expr const & _e2) {
        expr e1 = fast_normalize(_e1);
        expr e2 = fast_normalize(_e2);

        mpq q1, q2;
        if (is_mpq_macro(e2, q2)) {
            if (q2.is_zero()) {
                if (m_im->is_discrete_field() || current_type_is_nat() || current_type_is_int())
                    return m_im->get_zero();
                else
                    return mk_app(m_im->get_div(), e1, e2);
            } else if (is_mpq_macro(e1, q1)) {
                return mk_mod_mpq_macro(*m_im, q1/q2);
            } else {
                q2.inv();
                return mk_app(m_im->get_mul(), mk_mod_mpq_macro(*m_im, q2), e1);
            }
        }

        // theorem field.div_mul_div (a : A) {b : A} (c : A) {d : A} (Hb : b ≠ 0) (Hd : d ≠ 0) :
        // (a / b) * (c / d) = (a * c) / (b * d)
        if (m_im->is_field()) {
            expr a1, v1, a2, v2;
            if (is_mul(e1, a1, v1) && is_mpq_macro(a1, q1)) {
                // already <num> * <other>
            } else {
                q1 = 1/1;
                v1 = e1;
            }

            if (is_mul(e2, a2, v2) && is_mpq_macro(a2, q2)) {
                // already <num> * <other>
            } else {
                q2 = 1/1;
                v2 = e2;
            }

            if (q1 != 1 || q2 != 1) {
                q1 /= q2;
                return mk_app(m_im->get_mul(), mk_mod_mpq_macro(*m_im, q1),
                              mk_app(m_im->get_div(), v1, v2));
            }
        }

        // Note: we don't currently bother re-using original expression if it fails to simplify
        // If we did, we would need to check that the instances matched.
        return mk_app(m_im->get_div(), e1, e2);
    }

    void fast_get_flattened_nary_summands(expr const & e, buffer<expr> & args, bool normalize_children, bool * updated = nullptr) {
        expr arg1, arg2;
        if (is_add(e, arg1, arg2)) {
            fast_get_flattened_nary_summands(arg1, args, normalize_children, updated);
            fast_get_flattened_nary_summands(arg2, args, normalize_children, updated);
        } else if (normalize_children) {
            bool process_summands = false;
            expr e_n = fast_normalize(e, process_summands);

            if (updated != nullptr && e != e_n)
                *updated = true;

            if (is_add(e_n, arg1, arg2)) {
                fast_get_flattened_nary_summands(arg1, args, normalize_children, updated);
                fast_get_flattened_nary_summands(arg2, args, normalize_children, updated);
            } else {
                args.push_back(e_n);
            }
        } else {
            args.push_back(e);
        }
    }

    void fast_get_flattened_nary_multiplicands(expr const & e, buffer<expr> & args, bool normalize_children = true) {
        expr arg1, arg2;
        if (is_mul(e, arg1, arg2)) {
            fast_get_flattened_nary_multiplicands(arg1, args, normalize_children);
            fast_get_flattened_nary_multiplicands(arg2, args, normalize_children);
        } else if (normalize_children) {
            bool process_summands = true;
            bool process_multiplicands = false;
            expr e_n = fast_normalize(e, process_summands, process_multiplicands);
            if (is_mul(e_n, arg1, arg2)) {
                fast_get_flattened_nary_multiplicands(arg1, args, normalize_children);
                fast_get_flattened_nary_multiplicands(arg2, args, normalize_children);
            } else {
                args.push_back(e_n);
            }
        } else {
            args.push_back(e);
        }
    }

    expr fast_normalize_add(expr const & e, bool process_summands, bool normalize_children) {
        buffer<expr> monomials;
        bool updated = false;
        fast_get_flattened_nary_summands(e, monomials, normalize_children, &updated);

        if (!process_summands) {
            if (!updated)
                return e;
            else
                return mk_polynomial(*m_im, monomials);
        }

        expr_struct_set power_products;
        expr_struct_set repeated_power_products;

        mpq coeff;
        mpq num;
        unsigned num_coeffs = 0;

        for (expr const & monomial : monomials) {
            if (is_mpq_macro(monomial, num)) {
                coeff += num;
                num_coeffs++;
            } else {
                expr power_product = get_power_product(monomial);
                if (power_products.count(power_product)) {
                    repeated_power_products.insert(power_product);
                } else {
                    power_products.insert(power_product);
                }
            }
        }

        if (!updated && num_coeffs == 0 && repeated_power_products.empty())
            return e;

        buffer<expr> new_monomials;
        if (repeated_power_products.empty()) {
            // Only numerals may need to be fused
            for (expr const & monomial : monomials) {
                if (!is_mpq_macro(monomial)) {
                    new_monomials.push_back(monomial);
                }
            }
            expr e_n = mk_polynomial(*m_im, coeff, new_monomials);
            lean_trace_d(name({"arith_normalizer", "fast", "normalize_add"}), tout() << e << " ==> " << e_n << "\n";);
            return e_n;
        } else {
            lean_assert(!repeated_power_products.empty());
            expr_struct_map<mpq> power_product_to_coeff;

            for (expr const & monomial : monomials) {
                if (is_mpq_macro(monomial))
                    continue;
                expr power_product = get_power_product(monomial, num);
                if (!repeated_power_products.count(power_product))
                    continue;
                power_product_to_coeff[power_product] += num;
            }

            power_products.clear();

            for (expr const & monomial : monomials) {
                if (is_mpq_macro(monomial))
                    continue;
                expr power_product = get_power_product(monomial, num);
                if (!repeated_power_products.count(power_product)) {
                    new_monomials.push_back(monomial);
                } else if (!power_products.count(power_product)) {
                    power_products.insert(power_product);
                    mpq c = power_product_to_coeff.at(power_product);
                    if (!c.is_zero())
                        new_monomials.push_back(mk_monomial(*m_im, c, power_product));
                }
            }
            expr e_n = mk_polynomial(*m_im, coeff, new_monomials);
            lean_trace_d(name({"arith_normalizer", "fast", "normalize_add"}), tout() << e << " ==> " << e_n << "\n";);
            return e_n;
        }
    }

    void get_normalized_add_summands(expr const & e, buffer<expr> & summands) {
        expr first, rest;
        if (is_add(e, first, rest)) {
            lean_assert(!is_add(first));
            summands.push_back(first);
            get_normalized_add_summands(rest, summands);
        } else {
            summands.push_back(e);
        }
    }

    expr fast_normalize_mul(expr const & e) {
        buffer<expr> multiplicands;
        fast_get_flattened_nary_multiplicands(e, multiplicands);
        expr e_n = fast_normalize_mul_core(multiplicands);
        lean_trace_d(name({"arith_normalizer", "fast", "normalize_mul"}), tout() << e << " ==> " << e_n << "\n";);
        return e_n;
    }

    expr fast_normalize_mul_core(buffer<expr> const & multiplicands) {
        mpq coeff(1);
        mpq num;
        unsigned num_coeffs = 0;
        unsigned num_add    = 0;

        buffer<expr> non_num_multiplicands;

        for (expr const & multiplicand : multiplicands) {
            if (is_mpq_macro(multiplicand, num)) {
                coeff *= num;
                num_coeffs++;
            } else {
                non_num_multiplicands.push_back(multiplicand);
                if (is_add(multiplicand))
                    num_add++;
            }
        }

        if (coeff.is_zero()) {
            return mk_monomial(*m_im, coeff);
        } else if (non_num_multiplicands.empty()) {
            return mk_monomial(*m_im, coeff);
        }

        // TODO(dhs): expr_pow_lt
        // TODO(dhs): detect special cases and return early

        expr e_n;
        if (!m_options.m_distribute_mul || num_add == 0) {
            std::sort(non_num_multiplicands.begin(), non_num_multiplicands.end());
            e_n = mk_monomial(*m_im, coeff, mk_nary_app(m_im->get_mul(), non_num_multiplicands));
        } else {
            // TODO(dhs): use buffer<expr &> instead, to avoid all the reference counting
            lean_assert(m_options.m_distribute_mul);
            lean_assert(num_add > 0);

            buffer<unsigned> sizes;
            buffer<unsigned> iter;
            buffer<buffer<expr>> sums;

            for (expr const & multiplicand : non_num_multiplicands) {
                iter.push_back(0);
                buffer<expr> sum;
                if (is_add(multiplicand)) {
                    get_normalized_add_summands(multiplicand, sum);
                    sums.push_back(sum);
                    sizes.push_back(sum.size());
                } else {
                    sum.push_back(multiplicand);
                    sizes.push_back(1);
                    sums.push_back(sum);
                    lean_assert(sums.back()[0] == multiplicand);
                }
            }

            buffer<expr> new_multiplicands;

            buffer<expr> tmp;
            do {
                tmp.clear();
                tmp.push_back(mk_mod_mpq_macro(*m_im, coeff));
                bool normalize_children = false;
                for (unsigned i = 0; i < non_num_multiplicands.size(); ++i) {
                    fast_get_flattened_nary_multiplicands(sums[i][iter[i]], tmp, normalize_children);
                }
                new_multiplicands.push_back(fast_normalize_mul_core(tmp));
            } while (product_iterator_next(sizes, iter));
            e_n = mk_nary_app(m_im->get_add(), new_multiplicands);
        }
        return e_n;
    }

    void fast_cancel_monomials(expr const & lhs, expr const & rhs, expr & new_lhs, expr & new_rhs) {
        buffer<expr> lhs_monomials;
        buffer<expr> rhs_monomials;
        bool process_summands = false;
        bool normalize_children = false;
        fast_get_flattened_nary_summands(fast_normalize(lhs, process_summands), lhs_monomials, normalize_children);
        fast_get_flattened_nary_summands(fast_normalize(rhs, process_summands), rhs_monomials, normalize_children);
        bool orient_polys = m_options.m_orient_polys && m_im->is_comm_ring();

        buffer<expr> new_lhs_monomials, new_rhs_monomials;
        mpq coeff;
        fast_cancel_monomials_core(lhs_monomials, rhs_monomials, new_lhs_monomials, new_rhs_monomials, coeff, orient_polys);

        bool coeff_on_rhs = orient_polys || new_rhs_monomials.empty() || !new_lhs_monomials.empty();
        if (coeff_on_rhs) {
            new_lhs = mk_polynomial(*m_im, new_lhs_monomials);
            new_rhs = mk_polynomial(*m_im, neg(coeff), new_rhs_monomials);
        } else {
            new_lhs = mk_polynomial(*m_im, coeff, new_lhs_monomials);
            new_rhs = mk_polynomial(*m_im, new_rhs_monomials);
        }
        lean_trace_d(name({"arith_normalizer", "fast", "cancel_monomials"}), tout() << lhs << " <> " << rhs << " ==> " << new_lhs << " <> " << new_rhs << "\n";);
    }

    void fast_cancel_monomials_core(buffer<expr> const & lhs_monomials, buffer<expr> const & rhs_monomials,
                                    buffer<expr> & new_lhs_monomials, buffer<expr> & new_rhs_monomials,
                                    mpq & coeff, bool orient_polys) {
        // Pass 1: collect numerals, determine which power products appear on both sides
        expr_struct_set lhs_power_products;// shared?
        expr_struct_map<mpq> power_product_to_coeff;

        mpq num;
        unsigned num_coeffs = 0;

        for (expr const & monomial : lhs_monomials) {
            if (is_mpq_macro(monomial, num)) {
                coeff += num;
                num_coeffs++;
            } else {
                expr power_product = get_power_product(monomial, num);
                lhs_power_products.insert(power_product);
                auto it = power_product_to_coeff.find(power_product);
                if (it != power_product_to_coeff.end())
                    it->second += num;
                else
                    power_product_to_coeff.insert({power_product, num});
            }
        }

        for (expr const & monomial : rhs_monomials) {
            if (is_mpq_macro(monomial, num)) {
                coeff -= num;
                num_coeffs++;
            } else {
                expr power_product = get_power_product(monomial, num);
                if (lhs_power_products.count(power_product) || orient_polys) {
                    auto it = power_product_to_coeff.find(power_product);
                    if (it != power_product_to_coeff.end()) {
                        it->second -= num;
                    } else {
                        num.neg();
                        power_product_to_coeff.insert({power_product, num});
                    }
                } else {
                    auto it = power_product_to_coeff.find(power_product);
                    if (it != power_product_to_coeff.end())
                        it->second += num;
                    else
                        power_product_to_coeff.insert({power_product, num});
                }
            }
        }

        lhs_power_products.clear();
        for (expr const & monomial : lhs_monomials) {
            if (is_mpq_macro(monomial))
                continue;
            expr power_product = get_power_product(monomial, num);
            if (lhs_power_products.count(power_product))
                continue;
            lhs_power_products.insert(power_product);
            mpq & c = power_product_to_coeff[power_product];
            if (!c.is_zero())
                new_lhs_monomials.push_back(mk_monomial(*m_im, c, power_product));
        }

        expr_struct_set rhs_visited;
        for (expr const & monomial : rhs_monomials) {
            if (is_mpq_macro(monomial))
                continue;
            expr power_product = get_power_product(monomial);
            if (lhs_power_products.count(power_product) || rhs_visited.count(power_product))
                continue;

            rhs_visited.insert(power_product);
            mpq & c = power_product_to_coeff[power_product];
            if (c.is_zero())
                continue;
            if (orient_polys)
                new_lhs_monomials.push_back(mk_monomial(*m_im, c, power_product));
            else
                new_rhs_monomials.push_back(mk_monomial(*m_im, c, power_product));
        }
    }
};

// Entry points
expr fast_arith_normalize(type_context & tctx, expr const & lhs, arith_normalize_options const & options) {
    return fast_arith_normalize_fn(tctx, options)(lhs);
}

// Setup and teardown
void initialize_fast_arith_normalizer() {}
void finalize_fast_arith_normalizer() {}


}
