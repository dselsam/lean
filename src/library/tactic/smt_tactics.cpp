/*
Copyright (c) 2016 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include <cstdio>
#include <iostream>
#include <fstream>
#include <memory>
#include <stdexcept>
#include <string>
#include "util/sstream.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_string.h"
#include "library/exception.h"
#include "library/constants.h"
#include "library/num.h"
#include "library/util.h"
#include "library/kernel_serializer.h"
#include "library/tactic/tactic_state.h"

namespace lean {

static atomic<unsigned> g_next_idx{0};
static const std::string g_tmp_prefix{".smt"};
static std::string next_filename() { return g_tmp_prefix + std::to_string(g_next_idx++); }

static const std::string z3_cmd_prefix{"z3 --smt2 "};
static std::string z3_cmd(std::string const & filename) { return z3_cmd_prefix + filename; }

/* Note: this solution was copied from
   http://stackoverflow.com/questions/478898/how-to-execute-a-command-and-get-output-of-command-within-c-using-posix
   TODO(dhs): move this to /util? */
std::string exec(const char * cmd) {
    char buffer[128];
    std::string result = "";
    std::shared_ptr<FILE> pipe(popen(cmd, "r"), pclose);
    if (!pipe)
        throw std::runtime_error("popen() failed!");
    while (!feof(pipe.get())) {
        if (fgets(buffer, 128, pipe.get()) != NULL)
            result += buffer;
    }
    return result;
}

// Macro for trusting Z3
static name * g_z3_macro_name    = nullptr;
static std::string * g_z3_opcode = nullptr;

class z3_macro_definition_cell : public macro_definition_cell {
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 1)
            throw exception(sstream() << "invalid 'z3' macro, incorrect number of arguments");
    }
public:
    z3_macro_definition_cell() {}

    virtual name get_name() const override { return *g_z3_macro_name; }
    virtual expr check_type(expr const & m, abstract_type_context &, bool) const override {
        check_macro(m);
        return macro_arg(m, 0);
    }

    virtual optional<expr> expand(expr const & m, abstract_type_context & /* tctx */) const override {
        check_macro(m);
        // Note: the z3 macro will never be able to expand
        return none_expr();
    }

    virtual void write(serializer & s) const override {
        s.write_string(*g_z3_opcode);
    }

    virtual bool operator==(macro_definition_cell const & other) const override {
        if (dynamic_cast<z3_macro_definition_cell const *>(&other)) {
            return true;
        } else {
            return false;
        }
    }

    virtual unsigned hash() const override {
        return get_name().hash();
    }
};

expr mk_z3_macro(expr const & thm) {
    macro_definition m(new z3_macro_definition_cell());
    return mk_macro(m, 1, &thm);
}


// Exposed VM functions
vm_obj trust_z3(vm_obj const & vm_s) {
    tactic_state s = to_tactic_state(vm_s);
    return mk_tactic_success(to_obj(mk_z3_macro(mk_false())), s);
}

vm_obj call_z3(vm_obj const & vm_input, vm_obj const & vm_s) {
    tactic_state s = to_tactic_state(vm_s);
    std::string input = to_string(vm_input);
    std::string filename = next_filename();
    std::string cmd = z3_cmd(filename);

    {
        std::ofstream os(filename.c_str());
        if (os)
            os << input;
        else
            return mk_tactic_exception(sstream() << "Unable to open temporary file '" << filename << "' when calling `z3`", s);
    }

    std::string output;
    try {
        output = exec(cmd.c_str());
    } catch (exception & ex) {
        return mk_tactic_exception("Error when calling `z3`", s);
    }

    std::remove(filename.c_str());
    return mk_tactic_success(to_obj(output), s);
}

// Numeral Macro
// TODO(dhs): not the best place for this

struct concrete_arith_type {
    enum class kind { BitVec, Real, Int, nat };
    kind m_kind;
    optional<mpz>  m_bv_sz;

    concrete_arith_type() {}
    concrete_arith_type(kind k): m_kind(k) {}
    concrete_arith_type(mpz sz): m_kind(kind::BitVec), m_bv_sz(sz) {}

    kind get_kind() const { return m_kind; }
    optional<mpz> get_bv_sz() const { return m_bv_sz; }

    expr get_type() const {
        switch (m_kind) {
        case concrete_arith_type::kind::Int:    return mk_constant(get_Int_name());
        case concrete_arith_type::kind::Real:   return mk_constant(get_Real_name());
        case concrete_arith_type::kind::nat:    return mk_constant(get_nat_name());
        case concrete_arith_type::kind::BitVec: return mk_app(mk_constant(get_BitVec_name()), to_nat_expr(*m_bv_sz));
        }
        lean_unreachable();
    }

    expr mpz2expr(mpz const & n) const {
        expr type, has_zero, has_one, has_add;
        switch (m_kind) {
        case concrete_arith_type::kind::Int:
            type     = mk_constant(get_Int_name());
            has_zero = mk_constant(get_Int_has_zero_name());
            has_one  = mk_constant(get_Int_has_one_name());
            has_add  = mk_constant(get_Int_has_add_name());
            break;
        case concrete_arith_type::kind::Real:
            type     = mk_constant(get_Real_name());
            has_zero = mk_constant(get_Real_has_zero_name());
            has_one  = mk_constant(get_Real_has_one_name());
            has_add  = mk_constant(get_Real_has_add_name());
            break;
        case concrete_arith_type::kind::nat:
            type     = mk_constant(get_nat_name());
            has_zero = mk_constant(get_nat_has_zero_name());
            has_one  = mk_constant(get_nat_has_one_name());
            has_add  = mk_constant(get_nat_has_add_name());
            break;
        case concrete_arith_type::kind::BitVec:
            type     = mk_app(mk_constant(get_BitVec_name()), to_nat_expr(*get_bv_sz()));
            has_zero = mk_app(mk_constant(get_BitVec_has_zero_name()), to_nat_expr(*get_bv_sz()));
            has_one  = mk_app(mk_constant(get_BitVec_has_one_name()), to_nat_expr(*get_bv_sz()));
            has_add  = mk_app(mk_constant(get_BitVec_has_add_name()), to_nat_expr(*get_bv_sz()));
            break;
        }
        expr zero = mk_app({mk_constant(get_zero_name(), {mk_level_one()}), type, has_zero});
        expr one  = mk_app({mk_constant(get_one_name(), {mk_level_one()}), type, has_one});
        expr bit0 = mk_app({mk_constant(get_bit0_name(), {mk_level_one()}), type, has_add});
        expr bit1 = mk_app({mk_constant(get_bit1_name(), {mk_level_one()}), type, has_one, has_add});

        if (n.is_zero())
            return zero;
        return posmpz2expr(one, bit0, bit1, n);
    }

    expr posmpz2expr(expr one, expr bit0, expr bit1, mpz const & n) const {
        lean_assert(n > 0);
        if (n == 1)
            return one;
        if (n % mpz(2) == 1)
            return mk_app(bit1, posmpz2expr(one, bit0, bit1, n/2));
        else
            return mk_app(bit0, posmpz2expr(one, bit0, bit1, n/2));
    }

};

bool operator==(concrete_arith_type const & cty1, concrete_arith_type const & cty2) {
    return cty1.get_kind() == cty2.get_kind() && cty1.get_bv_sz() == cty2.get_bv_sz();
}
inline bool operator!=(concrete_arith_type const & cty1, concrete_arith_type const & cty2) { return !operator==(cty1, cty2); }

inline serializer & operator<<(serializer & s, concrete_arith_type cty) {
    s << static_cast<char>(cty.get_kind());
    write_optional<mpz>(s, cty.get_bv_sz());
    return s;
}

inline deserializer & operator>>(deserializer & d, concrete_arith_type & cty) {
    char c;
    d >> c;
    cty.m_kind = static_cast<concrete_arith_type::kind>(c);
    cty.m_bv_sz = read_optional<mpz>(d);
    return d;
}

// TODO(dhs): move to VM module?
mpz nat_to_mpz(vm_obj const & o) {
    if (is_simple(o))
        return mpz(cidx(o));
    else
        return to_mpz(o);
}

concrete_arith_type to_concrete_arith_type(vm_obj const & o) {
    switch (cidx(o)) {
    case 0: return concrete_arith_type(concrete_arith_type::kind::Int);
    case 1: return concrete_arith_type(concrete_arith_type::kind::Real);
    case 2: return concrete_arith_type(concrete_arith_type::kind::nat);
    case 3: return concrete_arith_type(nat_to_mpz(cfield(o, 0)));
    }
    lean_unreachable();
}

vm_obj to_obj(concrete_arith_type const & cty) {
    switch (cty.get_kind()) {
    case concrete_arith_type::kind::Int:    return mk_vm_simple(0);
    case concrete_arith_type::kind::Real:   return mk_vm_simple(1);
    case concrete_arith_type::kind::nat:    return mk_vm_simple(2);
    case concrete_arith_type::kind::BitVec: return mk_vm_constructor(3, mk_vm_nat(*cty.get_bv_sz()));
    }
    lean_unreachable();
}

static name * g_smt_mpz_macro_name    = nullptr;
static std::string * g_smt_mpz_opcode = nullptr;

class smt_mpz_macro_definition_cell : public macro_definition_cell {
    mpz                 m_z;
    concrete_arith_type m_cty;

    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 0)
            throw exception(sstream() << "invalid 'smt_mpz' macro, no arguments expected");
    }

public:
    smt_mpz_macro_definition_cell(mpz const & z, concrete_arith_type const & cty):
        m_z(z), m_cty(cty) {}

    mpz const & get_mpz() const { return m_z; }
    concrete_arith_type const & get_concrete_arith_type() const { return m_cty; }

    virtual name get_name() const { return *g_smt_mpz_macro_name; }
    virtual expr check_type(expr const & m, abstract_type_context &, bool) const {
        check_macro(m);
        return m_cty.get_type();
    }

    virtual optional<expr> expand(expr const & m, abstract_type_context &) const {
        check_macro(m);
        return some_expr(m_cty.mpz2expr(m_z));
    }

    virtual void write(serializer & s) const {
        s.write_string(*g_smt_mpz_opcode);
        s << m_z << m_cty;
    }

    virtual bool operator==(macro_definition_cell const & other) const {
        if (auto other_ptr = dynamic_cast<smt_mpz_macro_definition_cell const *>(&other)) {
            return get_mpz() == other_ptr->get_mpz()
                && get_concrete_arith_type() == other_ptr->get_concrete_arith_type();
        } else {
            return false;
        }
    }

    virtual unsigned hash() const {
        return ::lean::hash(get_name().hash(), m_z.hash());
    }
};

expr mk_smt_mpz_macro(mpz const & z, concrete_arith_type const & cty) {
    macro_definition m(new smt_mpz_macro_definition_cell(z, cty));
    return mk_macro(m);
}

vm_obj mk_smt_numeral_macro(vm_obj const & vm_n, vm_obj const & vm_cty) {
    mpz z = nat_to_mpz(vm_n);
    concrete_arith_type cty = to_concrete_arith_type(vm_cty);
    return to_obj(mk_smt_mpz_macro(z, cty));
}

vm_obj is_smt_numeral_macro(vm_obj const & vm_e) {
    expr e = to_expr(vm_e);
    if (is_macro(e)) {
        if (auto def = dynamic_cast<smt_mpz_macro_definition_cell const *>(macro_def(e).raw())) {
            return mk_vm_constructor(1, mk_vm_pair(mk_vm_nat(def->get_mpz()), to_obj(def->get_concrete_arith_type())));
        } else {
            return mk_vm_simple(0);
        }
    } else {
        return mk_vm_simple(0);
    }
}

void initialize_smt_tactics() {
    g_z3_macro_name = new name("z3");
    g_z3_opcode     = new std::string("Z3");
    register_macro_deserializer(*g_z3_opcode,
                                [](deserializer & /* d */, unsigned num, expr const * args) {
                                    if (num != 1)
                                        throw corrupted_stream_exception();
                                    return mk_z3_macro(args[0]);
                                });

    DECLARE_VM_BUILTIN(name({"tactic", "smt", "trustZ3"}), trust_z3);
    DECLARE_VM_BUILTIN(name({"tactic", "smt", "callZ3"}), call_z3);

    g_smt_mpz_macro_name = new name("smt_mpz");
    g_smt_mpz_opcode     = new std::string("SMT_MPZ");
    register_macro_deserializer(*g_smt_mpz_opcode,
                                [](deserializer & d, unsigned num, expr const *) {
                                    if (num != 0)
                                        throw corrupted_stream_exception();
                                    mpz z;
                                    concrete_arith_type cty;
                                    d >> z;
                                    d >> cty;
                                    return mk_smt_mpz_macro(z, cty);
                                });

    DECLARE_VM_BUILTIN(name({"tactic", "smt", "mkNumeralMacro"}), mk_smt_numeral_macro);
    DECLARE_VM_BUILTIN(name({"tactic", "smt", "isNumeralMacro"}), is_smt_numeral_macro);
}

void finalize_smt_tactics() {
    delete g_z3_macro_name;
    delete g_z3_opcode;
    delete g_smt_mpz_macro_name;
    delete g_smt_mpz_opcode;
}

}
