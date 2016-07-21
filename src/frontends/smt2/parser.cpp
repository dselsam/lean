/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include <string>
#include <stack>
#include <utility>
#include <vector>
#include "util/flet.h"
#include "util/name_map.h"
#include "util/exception.h"
#include "kernel/environment.h"
#include "kernel/declaration.h"
#include "kernel/type_checker.h"
#include "kernel/expr_maps.h"
#include "kernel/pos_info_provider.h"
#include "library/constants.h"
#include "library/io_state.h"
#include "library/io_state_stream.h"
#include "library/local_context.h"
#include "frontends/smt2/scanner.h"
#include "frontends/smt2/parser.h"

namespace lean {
namespace smt2 {

// Theory symbols
// TODO(dhs): I may not actually do it this way, and instead just have a chain of IF statements.
static std::unordered_map<std::string, expr> * g_pure_theory_symbols        = nullptr;
static std::unordered_map<std::string, expr> * g_polymorphic_theory_symbols = nullptr;

// Reserved words
// (a) General
static char const * g_token_as          = "as";
static char const * g_token_binary      = "BINARY";
static char const * g_token_decimal     = "DECIMAL";
static char const * g_token_exists      = "exists";
static char const * g_token_hexadecimal = "HEXADECIMAL";
static char const * g_token_forall      = "forall";
static char const * g_token_let         = "let";
static char const * g_token_numeral     = "NUMERAL";
static char const * g_token_par         = "par";
static char const * g_token_string      = "STRING";

// (b) Command names
static char const * g_token_assert                = "assert";
static char const * g_token_check_sat             = "check-sat";
static char const * g_token_check_sat_assuming    = "check-sat-assuming";
static char const * g_token_declare_const         = "declare-const";
static char const * g_token_declare_fun           = "declare-fun";
static char const * g_token_declare_sort          = "declare-sort";
static char const * g_token_define_fun            = "define-fun";
static char const * g_token_define_fun_rec        = "define-fun-rec";
static char const * g_token_define_funs_rec       = "define-fun-rec";
static char const * g_token_define_sort           = "define-sort";
static char const * g_token_echo                  = "echo";
static char const * g_token_exit                  = "exit";
static char const * g_token_get_assertions        = "get-assertions";
static char const * g_token_get_assignment        = "get-assignment";
static char const * g_token_get_info              = "get-info";
static char const * g_token_get_model             = "get-model";
static char const * g_token_get_option            = "get-option";
static char const * g_token_get_proof             = "get-proof";
static char const * g_token_get_unsat_assumptions = "get-unsat-assumptions";
static char const * g_token_get_unsat_core        = "get-unsat-core";
static char const * g_token_get_value             = "get-value";
static char const * g_token_pop                   = "pop";
static char const * g_token_push                  = "push";
static char const * g_token_reset                 = "reset";
static char const * g_token_reset_assertions      = "reset-assertions";
static char const * g_token_set_info              = "set-info";
static char const * g_token_set_logic             = "set-logic";
static char const * g_token_set_option            = "set-option";

// TODO(dhs): we need to create a unique name here
// Note: the issue is that sort names in a different namespace than term names
static char const * g_sort_name_prefix            = "#sort";
static name mk_sort_name(symbol const & s) { return name({g_sort_name_prefix, s.c_str()}); }

// Parser class
class parser {
private:
    io_state                m_ios;
    scanner                 m_scanner;

    std::stack<environment> m_env_stack;

    bool                    m_use_exceptions;
    unsigned                m_num_open_paren{0};
    scanner::token_kind     m_curr_kind{scanner::token_kind::BEGIN};

    // Util
    std::string const & get_stream_name() const { return m_scanner.get_stream_name(); }

    [[ noreturn ]] void throw_parser_exception(char const * msg, pos_info p) {
        throw parser_exception(msg, get_stream_name().c_str(), p.first, p.second);
    }

    void throw_parser_exception(std::string const & msg, pos_info p) { throw_parser_exception(msg.c_str(), p); }
    void throw_parser_exception(std::string const & msg) { throw_parser_exception(msg.c_str(), m_scanner.get_pos_info()); }
    void throw_parser_exception(char const * msg) { throw_parser_exception(msg, m_scanner.get_pos_info()); }

    // TODO(dhs): implement!
    expr elaborate(expr const & e) { return e; }

    environment & env() {
        lean_assert(!m_env_stack.empty());
        return m_env_stack.top();
    }

    scanner::token_kind curr_kind() const { return m_curr_kind; }
    std::string const & curr_string() const { return m_scanner.get_str_val(); }
    symbol const & curr_symbol() const { return m_scanner.get_symbol_val(); }
    mpq const & curr_numeral() const { return m_scanner.get_num_val(); }

    void scan() {
        switch (curr_kind()) {
        case scanner::token_kind::LEFT_PAREN: m_num_open_paren++; break;
        case scanner::token_kind::RIGHT_PAREN: m_num_open_paren--; break;
        default: break;
        }
        m_curr_kind = m_scanner.scan();
    }

    void next() { if (m_curr_kind != scanner::token_kind::END) scan(); }

    void check_curr_kind(scanner::token_kind kind, char const * msg, pos_info p = pos_info()) {
        if (curr_kind() != kind)
            throw_parser_exception(msg, p);
    }

    // Parser helpers
    expr parse_expr(bool is_sort, char const * context) {
        if (curr_kind() == scanner::token_kind::SYMBOL) {
            symbol sym = curr_symbol();
            auto it_pure = g_pure_theory_symbols->find(sym);
            if (it_pure != g_pure_theory_symbols->end()) {
                next();
                return it_pure->second;
            }
            auto it_poly = g_polymorphic_theory_symbols->find(sym);
            if (it_poly != g_polymorphic_theory_symbols->end()) {
                // TODO(dhs): these will need to be elaborated. I do not think we will be able to decide implicit arguments locally
                next();
                return it_poly->second;
            }
            next();
            return mk_constant(is_sort ? mk_sort_name(sym) : name(sym));
        } else if (curr_kind() == scanner::token_kind::LEFT_PAREN) {
            next();
            buffer<expr> args;
            parse_exprs(args, is_sort, context);
            return mk_app(args);
        } else {
            throw_parser_exception((std::string(context) + ", invalid expression").c_str());
        }
        lean_unreachable();
    }

    void parse_exprs(buffer<expr> & es, bool is_sort, char const * context) {
        while (curr_kind() != scanner::token_kind::RIGHT_PAREN) {
            es.push_back(parse_expr(is_sort, context));
        }
        if (es.empty()) {
            throw_parser_exception(std::string(context) + ", () not a legal expression");
        }
        next();
    }

    void parse_expr_list(buffer<expr> & es, bool is_sort, char const * context) {
        check_curr_kind(scanner::token_kind::LEFT_PAREN, context);
        next();
        parse_exprs(es, is_sort, context);
    }

    // Outer loop
    bool parse_commands() {

        try {
            scan();
        } catch (exception & e) {
            // TODO(dhs): try to recover from scanner errors
            throw e;
        }

        // TODO(dhs): for now we will not recover from any errors
        // This is reasonable for new given our goals for the parser:
        // we will be parsing well-established benchmarks that are highly unlikely to have errors in them.
        m_num_open_paren = 0;
        try {
            while (true) {
                switch (curr_kind()) {
                case scanner::token_kind::LEFT_PAREN:
                    parse_command();
                    break;
                case scanner::token_kind::END:
                    return true;
                default:
                    throw_parser_exception("invalid command, '(' expected", m_scanner.get_pos_info());
                    break;
                }
            }
        } catch (exception & e) {
            throw e;
        }
    }

    void parse_command() {
        lean_assert(curr_kind() == scanner::token_kind::LEFT_PAREN);
        pos_info pinfo = m_scanner.get_pos_info();
        next();
        check_curr_kind(scanner::token_kind::SYMBOL, "invalid command, symbol expected");
        const char * const s = m_scanner.get_str_val().c_str();
        if (s == g_token_assert)                     parse_assert();
        else if (s == g_token_check_sat)             parse_check_sat();
        else if (s == g_token_check_sat_assuming)    parse_check_sat_assuming();
        else if (s == g_token_declare_const)         parse_declare_const();
        else if (s == g_token_declare_fun)           parse_declare_fun();
        else if (s == g_token_declare_sort)          parse_declare_sort();
        else if (s == g_token_define_fun)            parse_define_fun();
        else if (s == g_token_define_fun_rec)        parse_define_fun_rec();
        else if (s == g_token_define_funs_rec)       parse_define_funs_rec();
        else if (s == g_token_define_sort)           parse_define_sort();
        else if (s == g_token_echo)                  parse_echo();
        else if (s == g_token_exit)                  parse_exit();
        else if (s == g_token_get_assertions)        parse_get_assertions();
        else if (s == g_token_get_assignment)        parse_get_assignment();
        else if (s == g_token_get_info)              parse_get_info();
        else if (s == g_token_get_model)             parse_get_model();
        else if (s == g_token_get_option)            parse_get_option();
        else if (s == g_token_get_proof)             parse_get_proof();
        else if (s == g_token_get_unsat_assumptions) parse_get_unsat_assumptions();
        else if (s == g_token_get_unsat_core)        parse_get_unsat_core();
        else if (s == g_token_get_value)             parse_get_value();
        else if (s == g_token_pop)                   parse_pop();
        else if (s == g_token_push)                  parse_push();
        else if (s == g_token_reset)                 parse_reset();
        else if (s == g_token_reset_assertions)      parse_reset_assertions();
        else if (s == g_token_set_info)              parse_set_info();
        else if (s == g_token_set_logic)             parse_set_logic();
        else if (s == g_token_set_option)            parse_set_option();
        else throw_parser_exception("unknown command", pinfo);
    }

    // Individual commands
    void parse_assert() { throw_parser_exception("assert not yet supported"); }
    void parse_check_sat() { throw_parser_exception("check-sat not yet supported"); }
    void parse_check_sat_assuming() { throw_parser_exception("check-sat-assuming not yet supported"); }
    void parse_declare_const() { throw_parser_exception("declare-const not yet supported"); }

    void parse_declare_fun() {
        lean_assert(curr_kind() == scanner::token_kind::SYMBOL);
        lean_assert(curr_symbol() == g_token_declare_fun);
        next();
        check_curr_kind(scanner::token_kind::SYMBOL, "invalid function declaration, symbol expected");
        name fn_name = name(curr_symbol());
        next();

        buffer<expr> parameter_sorts;
        bool is_sort = true;
        parse_expr_list(parameter_sorts, is_sort, "invalid function declaration");
        expr ty = elaborate(parse_expr(is_sort, "invalid function declaration"));
        for (int i = parameter_sorts.size() - 1; i >= 0; ++i) {
            ty = mk_arrow(elaborate(parameter_sorts[i]), ty);
        }

        declaration d = mk_axiom(fn_name, list<name>(), ty);
        env().add(check(env(), d));
        check_curr_kind(scanner::token_kind::RIGHT_PAREN, "invalid function declaration, ')' expected");
        next();
    }

    void parse_declare_sort() {
        lean_assert(curr_kind() == scanner::token_kind::SYMBOL);
        lean_assert(curr_symbol() == g_token_declare_sort);
        next();

        check_curr_kind(scanner::token_kind::SYMBOL, "invalid sort declaration, symbol expected");
        name sort_name = mk_sort_name(curr_symbol());
        if (env().find(sort_name)) {
            throw_parser_exception("invalid sort declaration, sort already declared/defined");
        }
        next();
        // Note: the official standard requires the arity, but it seems to be convention to have no arity mean 0
        mpq arity;
        if (curr_kind() == scanner::token_kind::RIGHT_PAREN) {
            // no arity means 0
        } else {
            check_curr_kind(scanner::token_kind::INT, "invalid sort declaration, arity (<numeral>) expected");
            arity = curr_numeral();
            // TODO(dhs): the standard does not put a limit on the arity, but a parametric sort that takes more than ten-thousand arguments is absurd
            // (arbitrary)
            if (arity > 10000) {
                throw_parser_exception("invalid sort declaration, arities greater than 10,000 not supported");
            }
            next();
        }

        expr ty = mk_Type();
        for (unsigned i = 0; i < arity; ++i) {
            ty = mk_arrow(mk_Type(), ty);
        }
        declaration d = mk_axiom(sort_name, list<name>(), ty);
        env().add(check(env(), d));
        check_curr_kind(scanner::token_kind::RIGHT_PAREN, "invalid sort declaration, ')' expected");
        next();
    }

    void parse_define_fun() { throw_parser_exception("define-fun not yet supported"); }
    void parse_define_fun_rec() { throw_parser_exception("define-fun-rec not yet supported"); }
    void parse_define_funs_rec() { throw_parser_exception("define-funs-rec not yet supported"); }
    void parse_define_sort() { throw_parser_exception("define-sort not yet supported"); }
    void parse_echo() { throw_parser_exception("echo not yet supported"); }
    void parse_exit() { throw_parser_exception("exit not yet supported"); }
    void parse_get_assertions() { throw_parser_exception("get-assertions not yet supported"); }
    void parse_get_assignment() { throw_parser_exception("get-assignment not yet supported"); }
    void parse_get_info() { throw_parser_exception("get-info not yet supported"); }
    void parse_get_model() { throw_parser_exception("get-model not yet supported"); }
    void parse_get_option() { throw_parser_exception("get-option not yet supported"); }
    void parse_get_proof() { throw_parser_exception("get-proof not yet supported"); }
    void parse_get_unsat_assumptions() { throw_parser_exception("get-unsat-assumptions not yet supported"); }
    void parse_get_unsat_core() { throw_parser_exception("get-unsat-core not yet supported"); }
    void parse_get_value() { throw_parser_exception("get-value not yet supported"); }
    void parse_pop() { throw_parser_exception("pop not yet supported"); }
    void parse_push() { throw_parser_exception("push not yet supported"); }
    void parse_reset() { throw_parser_exception("reset not yet supported"); }
    void parse_reset_assertions() { throw_parser_exception("reset-assertions not yet supported"); }
    void parse_set_info() { throw_parser_exception("set_info not yet supported"); }
    void parse_set_logic() { throw_parser_exception("set_logic not yet supported"); }
    void parse_set_option() { throw_parser_exception("set_option not yet supported"); }

public:

    // Constructor
    parser(environment const & env, io_state & ios, std::istream & strm, char const * strm_name, optional<std::string> const & base, bool use_exceptions):
        m_ios(ios), m_scanner(strm, strm_name), m_env_stack({env}), m_use_exceptions(use_exceptions) { }

    // Entry point
    bool operator()() { return parse_commands(); }
};

// Entry point
bool parse_commands(environment & env, io_state & ios, std::istream & strm, char const * fname, optional<std::string> const & base, bool use_exceptions) {
    parser p(env, ios, strm, fname, base, use_exceptions);
    return p();
}

void initialize_parser() {
    g_pure_theory_symbols = new std::unordered_map<std::string, expr>({
            // (a) Core
            {"Bool", mk_Prop()},
            {"true", mk_constant(get_true_name())},
            {"false", mk_constant(get_false_name())},
            {"not", mk_constant(get_not_name())},
            {"=>", mk_constant(get_implies_name())},
            {"and", mk_constant(get_and_name())},
            {"or", mk_constant(get_or_name())},
            {"xor", mk_constant(get_xor_name())},

            // (b) Arithmetic
            {"Int", mk_constant(get_int_name())},
            {"Real", mk_constant(get_real_name())},
            {"/", mk_constant(get_div_name())},

             // (c) Arrays
            {"Array", mk_constant(get_array_name())}, // TODO(dhs): may not exist yet
            {"select", mk_constant(get_array_select_name())}, // TODO(dhs): may not exist yet
            {"store", mk_constant(get_array_store_name())} // TODO(dhs): may not exist yet
        });

    g_polymorphic_theory_symbols = new std::unordered_map<std::string, expr>({
            // (a) Core
            {"=", mk_constant(get_eq_name())},

            // (b) Arithmetic
            {"+", mk_constant(get_add_name())},
            {"-", mk_constant(get_sub_name())},
            {"*", mk_constant(get_mul_name())},
            {"<", mk_constant(get_lt_name())},
            {"<=", mk_constant(get_le_name())},
            {">", mk_constant(get_gt_name())},
            {">=", mk_constant(get_ge_name())}
        });
}

void finalize_parser() {
    delete g_pure_theory_symbols;
    delete g_polymorphic_theory_symbols;
}

}}
