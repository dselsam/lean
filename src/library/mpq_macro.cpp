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
#include "library/kernel_serializer.h"
#include "library/type_context.h"
#include "library/app_builder.h"

namespace lean {

struct mpq2expr_fn {
    type_context & m_tctx;
    expr const & m_type;

    mpq2expr_fn(type_context & tctx, expr const & type): m_tctx(tctx), m_type(type) {}

    expr operator()(mpq const & q) {
        mpz numer = q.get_numerator();
        if (numer.is_zero())
            return mk_zero(m_tctx, m_type);

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
            e = mk_div(m_tctx, pos_mpz_to_expr(numer), pos_mpz_to_expr(denom));
        }

        if (flip_sign) {
            return mk_neg(m_tctx, e);
        } else {
            return e;
        }
    }

    expr pos_mpz_to_expr(mpz const & n) {
        lean_assert(n > 0);
        if (n == 1)
            return mk_one(m_tctx, m_type);
        if (n % mpz(2) == 1)
            return mk_bit1(m_tctx, pos_mpz_to_expr(n/2));
        else
            return mk_bit0(m_tctx, pos_mpz_to_expr(n/2));
    }
};

// Macro for trusting the fast normalizer
static name * g_mpq_macro_name    = nullptr;
static std::string * g_mpq_opcode = nullptr;

class mpq_macro_definition_cell : public macro_definition_cell {
    mpq m_q;

    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 1)
            throw exception(sstream() << "invalid 'mpq' macro, incorrect number of arguments");
    }

public:
    mpq_macro_definition_cell(mpq const & q): m_q(q) {}

    mpq const & get_mpq() const { return m_q; }
    virtual name get_name() const { return *g_mpq_macro_name; }
    virtual expr check_type(expr const & m, abstract_type_context & ctx, bool infer_only) const {
        check_macro(m);
        return macro_arg(m, 0);
    }

    virtual optional<expr> expand(expr const & m, abstract_type_context & ctx) const {
        check_macro(m);
        // TODO(dhs): create a new type context if necessary with the right local context
        return none_expr();
    }

    virtual void write(serializer & s) const {
        s.write_string(*g_mpq_opcode);
        s << m_q;
    }

    virtual bool operator==(macro_definition_cell const & other) const {
        // TODO(dhs): what is this used for?
        if (auto other_ptr = dynamic_cast<mpq_macro_definition_cell const *>(&other)) {
            return get_mpq() == other_ptr->get_mpq();
        } else {
            return false;
        }
    }

    virtual unsigned hash() const {
        return ::lean::hash(get_name().hash(), m_q.hash());
    }
};

expr mk_mpq_macro(mpq const & q, expr const & type) {
    macro_definition m(new mpq_macro_definition_cell(q));
    return mk_macro(m, 1, &type);
}

bool is_mpq_macro(expr const & e) {
    if (is_macro(e) && dynamic_cast<mpq_macro_definition_cell const *>(macro_def(e).raw()))
        return true;
    else
        return false;
}

bool is_mpq_macro(expr const & e, mpq & q) {
    if (is_macro(e)) {
        if (auto def = dynamic_cast<mpq_macro_definition_cell const *>(macro_def(e).raw())) {
            q = def->get_mpq();
            return true;
        } else {
            return false;
        }
    } else {
        return false;
    }
}

void initialize_mpq_macro() {
    g_mpq_macro_name = new name("mpq");
    g_mpq_opcode     = new std::string("MPQ");
    register_macro_deserializer(*g_mpq_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    if (num != 1)
                                        throw corrupted_stream_exception();
                                    mpq q;
                                    d >> q;
                                    return mk_mpq_macro(q, args[0]);
                                });
}

void finalize_mpq_macro() {
    delete g_mpq_macro_name;
    delete g_mpq_opcode;
}



}
