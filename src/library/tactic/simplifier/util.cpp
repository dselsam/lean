/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "kernel/expr.h"
#include "library/tactic/simplifier/util.h"

namespace lean {
/*
static name * g_flat_congr_simp_macro_name    = nullptr;
static std::string * g_flat_congr_simp_opcode = nullptr;

class flat_congr_simp_macro_definition_cell : public macro_definition_cell {
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) < 2)
            throw exception(sstream() << "invalid 'flat_congr_simp' macro, incorrect number of arguments");
        expr const & type = macro_arg(m, 0);
        bool ok_type = type == mk_constant(get_nat_name()) || type == mk_constant(get_int_name()) || type == mk_constant(get_real_name());
        if (!ok_type)
            throw exception(sstream() << "invalid 'flat_congr_simp' macro, only nat, int, and real accepted");
    }

public:
    flat_congr_simp_macro_definition_cell(flat_congr_simp const & q): m_q(q) {}

    flat_congr_simp const & get_flat_congr_simp() const { return m_q; }
    virtual name get_name() const { return *g_flat_congr_simp_macro_name; }
    virtual expr check_type(expr const & m, abstract_type_context &, bool) const {
        check_macro(m);
        return macro_arg(m, 0);
    }

    virtual optional<expr> expand(expr const & m, abstract_type_context &) const {
        check_macro(m);
        expr ty = macro_arg(m, 0);
        concrete_arith_type cty;
        if (ty == mk_constant(get_nat_name()))
            cty = concrete_arith_type::NAT;
        else if (ty == mk_constant(get_int_name()))
            cty = concrete_arith_type::INT;
        else if (ty == mk_constant(get_real_name()))
            cty = concrete_arith_type::REAL;
        else
            throw exception(sstream() << "trying to expand invalid 'flat_congr_simp' macro");

        return some_expr(flat_congr_simp2expr_fn(get_arith_instance_info_for(cty))(get_flat_congr_simp()));
    }

    virtual void write(serializer & s) const {
        s.write_string(*g_flat_congr_simp_opcode);
        s << m_q;
    }

    virtual bool operator==(macro_definition_cell const & other) const {
        if (auto other_ptr = dynamic_cast<flat_congr_simp_macro_definition_cell const *>(&other)) {
            return get_flat_congr_simp() == other_ptr->get_flat_congr_simp();
        } else {
            return false;
        }
    }

    virtual unsigned hash() const {
        return ::lean::hash(get_name().hash(), m_q.hash());
    }
};
*/
void initialize_simp_util() {
    // flat-congr-simp-macro
    /*
    g_flat_congr_simp_macro_name = new name("flat_congr_simp");
    g_flat_congr_simp_opcode     = new std::string("FLAT_CONGR_SIMP");
    register_macro_deserializer(*g_flat_congr_simp_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    if (num != 1)
                                        throw corrupted_stream_exception();
                                    flat_congr_simp q;
                                    d >> q;
                                    return mk_flat_congr_simp_macro(q, args[0]);
                                });
    */
}

void finalize_simp_util() {
    // flat-congr-simp-macro
    /*
    delete g_flat_congr_simp_macro_name;
    delete g_flat_congr_simp_opcode;
    */
}

// Entry points


expr mk_flat_congr_simp_macro(expr const & assoc, expr const & e_orig, buffer<simp_result> const & results, simp_result const & r_simp) {
    throw exception("NYI");
    return e_orig;
//    macro_definition m(new flat_congr_simp_macro_definition_cell(q));
//    return mk_macro(m, 1, &type);
}




}
