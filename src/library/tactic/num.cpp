/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include <string>
#include "util/sstream.h"
#include "util/hash.h"
#include "library/num.h"
#include "library/mpq_macro.h"
#include "library/constants.h"
#include "library/kernel_serializer.h"
#include "library/type_context.h"
#include "library/arith_instance_manager.h"

namespace lean {

struct mpq2expr_fn {
    arith_instance_info_ref m_info;

    mpq2expr_fn(arith_instance_info_ref info): m_info(info) {}

    expr operator()(mpq const & q) {
        mpz numer = q.get_numerator();
        if (numer.is_zero())
            return m_info->get_zero();

        mpz denom = q.get_denominator();
        lean_assert(denom > 0);

        bool flip_sign = false;
        if (numer.is_neg()) {
            numer.neg();
            flip_sign = true;
        }

        expr e;
        if (denom == 1) {
            e = pos_mpz_to_expr(numer);
        } else {
            e = mk_app(m_info->get_div(), pos_mpz_to_expr(numer), pos_mpz_to_expr(denom));
        }

        if (flip_sign) {
            return mk_app(m_info->get_neg(), e);
        } else {
            return e;
        }
    }

    expr pos_mpz_to_expr(mpz const & n) {
        lean_assert(n > 0);
        if (n == 1)
            return m_info->get_one();
        if (n % mpz(2) == 1)
            return mk_app(m_info->get_bit1(), pos_mpz_to_expr(n/2));
        else
            return mk_app(m_info->get_bit0(), pos_mpz_to_expr(n/2));
    }
};

expr mpq2expr(arith_instance_info_ref const & info, mpq const & q) {
    return mpq2expr_fn(info)(q);
}

}
