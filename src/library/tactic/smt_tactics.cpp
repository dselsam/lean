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


// Exposed VM functions
vm_obj trust_z3(vm_obj const & thm) { return to_obj(mk_z3_macro(to_expr(thm))); }

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

void initialize_smt_tactics() {
    g_z3_macro_name = new name("z3");
    g_z3_opcode     = new std::string("Z3");
    register_macro_deserializer(*g_z3_opcode,
                                [](deserializer & /* d */, unsigned num, expr const * args) {
                                    if (num != 1)
                                        throw corrupted_stream_exception();
                                    return mk_z3_macro(args[0]);
                                });

    DECLARE_VM_BUILTIN(name("trustZ3"), trust_z3);
    DECLARE_VM_BUILTIN(name({"tactic", "smt", "callZ3"}), call_z3);
}

void finalize_smt_tactics() {
    delete g_z3_macro_name;
    delete g_z3_opcode;
}

}
