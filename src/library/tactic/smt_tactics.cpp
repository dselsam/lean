/*
Copyright (c) 2016 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "util/sstream.h"
#include "library/vm/vm_expr.h"
#include "library/kernel_serializer.h"

namespace lean {

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
        // TODO(dhs): the z3 macro will never be able to expand
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

vm_obj vm_mk_z3_macro(vm_obj const & thm) { return to_obj(mk_z3_macro(to_expr(thm))); }

void initialize_smt_tactics() {
    g_z3_macro_name = new name("z3");
    g_z3_opcode     = new std::string("Z3");
    register_macro_deserializer(*g_z3_opcode,
                                [](deserializer & /* d */, unsigned num, expr const * args) {
                                    if (num != 1)
                                        throw corrupted_stream_exception();
                                    return mk_z3_macro(args[0]);
                                });

    DECLARE_VM_BUILTIN(name("trustZ3"), vm_mk_z3_macro);
}

void finalize_smt_tactics() {
    delete g_z3_macro_name;
    delete g_z3_opcode;
}

}
