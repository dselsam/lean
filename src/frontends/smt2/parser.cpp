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
#include "util/fresh_name.h"
#include "util/lean_path.h"
#include "kernel/environment.h"
#include "kernel/abstract.h"
#include "kernel/declaration.h"
#include "kernel/type_checker.h"
#include "kernel/expr_maps.h"
#include "kernel/pos_info_provider.h"
#include "library/constants.h"
#include "library/io_state.h"
#include "library/io_state_stream.h"
#include "library/local_context.h"
#include "library/module.h"
#include "library/trace.h"
#include "library/mpq_macro.h"
#include "library/tactic/tactic_state.h"
#include "frontends/smt2/scanner.h"
#include "frontends/smt2/parser.h"

namespace lean {
namespace smt2 {

static name * g_smt2_prefix;
static name * g_smt2_tactic;

enum class fun_attr { DEFAULT, LEFT_ASSOC, RIGHT_ASSOC, CHAINABLE, PAIRWISE };

struct fun_decl {
    expr     m_e;
    fun_attr m_fun_attr;
    fun_decl(expr const & e, fun_attr fattr): m_e(e), m_fun_attr(fattr) {}
    expr const & get_expr() const { return m_e; }
    fun_attr get_fun_attr() const { return m_fun_attr; }
};

static expr mk_left_assoc_app(buffer<expr> const & args) {
    lean_assert(args.size() >= 2);
    // f x1 x2 x3 ==> f (f x1 x2) x3
    expr e = mk_app(args[0], args[1], args[2]);
    for (unsigned i = 3; i < args.size(); ++i) {
        e = mk_app(args[0], e, args[i]);
    }
    return e;
}

static expr mk_right_assoc_app(buffer<expr> const & args) {
    lean_assert(args.size() >= 3);
    // f x1 x2 x3 ==> f x1 (f x2 x3)
    int k = args.size();
    expr e = mk_app(args[0], args[k - 2], args[k - 1]);
    for (int i = k - 3; i >= 0; --i) {
        e = mk_app(args[0], args[i], e);
    }
    return e;
}

static expr mk_chainable_app(buffer<expr> const & args) {
    // f x1 x2 x3 ==> and (f x1 x2) (f x2 x3)
    if (args.size() == 3) {
        return mk_app(args);
    }
    lean_assert(args.size() >= 3);
    buffer<expr> args_to_and;
    args_to_and.push_back(mk_constant(get_and_name()));
    for (unsigned i = 1; i < args.size() - 1; ++i) {
        args_to_and.push_back(mk_app(args[0], args[i], args[i+1]));
    }
    return mk_left_assoc_app(args_to_and);
}

// TODO(dhs): use a macro for this? It scales quadratically.
static expr mk_pairwise_app(buffer<expr> const & args) { throw exception("NYI"); }

// Theory symbols
// TODO(dhs): I may not actually do it this way, and instead just have a chain of IF statements.
static std::unordered_map<std::string, expr>     * g_theory_constant_symbols    = nullptr;
static std::unordered_map<std::string, fun_decl> * g_theory_function_symbols    = nullptr;

static optional<expr> is_theory_constant_symbol(std::string const & sym) {
    auto it = g_theory_constant_symbols->find(sym);
    if (it == g_theory_constant_symbols->end()) {
        return none_expr();
    } else {
        return some_expr(it->second);
    }
}

static optional<fun_decl> is_theory_function_symbol(std::string const & sym) {
    auto it = g_theory_function_symbols->find(sym);
    if (it == g_theory_function_symbols->end()) {
        return optional<fun_decl>();
    } else {
        return optional<fun_decl>(it->second);
    }
}

static char const * g_symbol_minus          = "-";
static char const * g_symbol_dependent_type = "_";

static char const * g_token_use_locals      = ":use_locals";


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


// Parser class
class parser {
private:
    environment             m_env;
    io_state                m_ios;

    local_context           m_lctx;

    scanner                 m_scanner;

    bool                    m_use_exceptions;
    unsigned                m_num_open_paren{0};
    scanner::token_kind     m_curr_kind{scanner::token_kind::BEGIN};

    bool                    m_use_locals{false};

    // Util
    std::string const & get_stream_name() const { return m_scanner.get_stream_name(); }

    [[ noreturn ]] void throw_parser_exception(char const * msg, pos_info p) {
        throw parser_exception(msg, get_stream_name().c_str(), p.first, p.second);
    }

    void throw_parser_exception(std::string const & msg, pos_info p) { throw_parser_exception(msg.c_str(), p); }
    void throw_parser_exception(std::string const & msg) { throw_parser_exception(msg.c_str(), m_scanner.get_pos_info()); }
    void throw_parser_exception(char const * msg) { throw_parser_exception(msg, m_scanner.get_pos_info()); }

    void register_hypothesis(name const & n, expr const & ty) {
        if (m_use_locals) {
            lctx().mk_local_decl(n, ty);
        } else {
            declaration d = mk_axiom(n, list<name>(), ty);
            m_env = env().add(check(env(), d));
        }
    }

    void register_hypothesis(expr const & ty) {
        name n = mk_tagged_fresh_name(*g_smt2_prefix);
        if (m_use_locals) {
            lctx().mk_local_decl(n, ty);
        } else {
            declaration d = mk_axiom(n, list<name>(), ty);
            m_env = env().add(check(env(), d));
        }
    }

    // Making bindings
    enum class binding_type { FORALL, EXISTS, LET };

    expr mk_binding(binding_type btype, buffer<expr> const & locals, expr const & e) { return mk_binding(btype, locals.size(), locals.data(), e); }

    expr mk_binding(binding_type btype, unsigned num_locals, expr const * locals, expr const & e) {
        buffer<local_decl>     decls;
        buffer<expr>           types;
        buffer<optional<expr>> values;
        for (unsigned i = 0; i < num_locals; i++) {
            local_decl const & decl = *lctx().get_local_decl(locals[i]);
            decls.push_back(decl);
            types.push_back(::lean::abstract_locals(decl.get_type(), i, locals));
            if (auto v = decl.get_value())
                values.push_back(some_expr(::lean::abstract_locals(*v, i, locals)));
            else
                values.push_back(none_expr());
        }
        expr new_e = ::lean::abstract_locals(e, num_locals, locals);
        lean_assert(types.size() == values.size());
        unsigned i = types.size();
        while (i > 0) {
            --i;
            switch (btype) {
            case binding_type::FORALL:
                lean_assert(!values[i]);
                new_e = ::lean::mk_pi(decls[i].get_pp_name(), types[i], new_e, decls[i].get_info());
                break;
            case binding_type::EXISTS:
                lean_assert(!values[i]);
                // @Exists.{l_1} ?A (λ (x : ?A), @eq.{l_1} ?A x x) : Prop
                new_e = mk_app(mk_constant(get_Exists_name(), {mk_level_one()}),
                               types[i],
                               ::lean::mk_lambda(decls[i].get_pp_name(), types[i], new_e, decls[i].get_info()));
                break;
            case binding_type::LET:
                lean_assert(values[i]);
                new_e = mk_let(decls[i].get_pp_name(), types[i], *values[i], new_e);
                break;
            }
        }
        return new_e;
    }

    // TODO(dhs): implement!
    // Note: Leo's elaborator will be called at the end
    expr pre_elaborate_app(buffer<expr> & args) {
        int num_args = args.size() - 1;
        lean_assert(num_args > 0);

        fun_attr fattr = fun_attr::DEFAULT;

        // Step 1: resolve function symbols in the operator expression
        // (constant symbols have already been resolved)
        if (is_constant(args[0])) {
            std::string op_str = const_name(args[0]).get_string();
            // One special case: (-) can be `neg` or `sub`
            if (op_str.c_str() == g_symbol_minus && num_args == 1) {
                args[0] = mk_constant(get_neg_name());
            } else if (auto fdecl = is_theory_function_symbol(op_str)) {
                args[0] = fdecl->get_expr();
                fattr = fdecl->get_fun_attr();
            }
        }

        switch (fattr) {
        case fun_attr::DEFAULT:
            return mk_app(args);
        case fun_attr::LEFT_ASSOC:
            return mk_left_assoc_app(args);
        case fun_attr::RIGHT_ASSOC:
            return mk_right_assoc_app(args);
        case fun_attr::CHAINABLE:
            return mk_chainable_app(args);
        case fun_attr::PAIRWISE:
            return mk_pairwise_app(args);
        }
        lean_unreachable();
    }

    environment & env() { return m_env; }
    io_state & ios() { return m_ios; }
    local_context & lctx() { return m_lctx; }

    scanner::token_kind curr_kind() const { return m_curr_kind; }
    std::string const & curr_string() const { return m_scanner.get_str_val(); }
    symbol const & curr_symbol() const { return m_scanner.get_symbol_val(); }
    mpq const & curr_numeral() const { return m_scanner.get_num_val(); }
    mpq curr_numeral_next() { mpq q = m_scanner.get_num_val(); next(); return q; }

    void scan() {
        switch (curr_kind()) {
        case scanner::token_kind::LEFT_PAREN: m_num_open_paren++; break;
        case scanner::token_kind::RIGHT_PAREN: m_num_open_paren--; break;
        default: break;
        }
        m_curr_kind = m_scanner.scan();
    }

    void next() { if (m_curr_kind != scanner::token_kind::END) scan(); }

    void check_curr_kind(scanner::token_kind kind, char const * msg) {
        if (curr_kind() != kind)
            throw_parser_exception(msg);
    }

    void check_curr_kind(scanner::token_kind kind, std::string const & msg) {
        if (curr_kind() != kind)
            throw_parser_exception(msg);
    }

    // Parser helpers
    // Parsing sorts
    void parse_sorted_var_list(buffer<expr> & bindings, char const * context) {
        check_curr_kind(scanner::token_kind::LEFT_PAREN, std::string(context) + ": sorted-var list expected");
        next();
        while (curr_kind() == scanner::token_kind::LEFT_PAREN) {
            next();
            check_curr_kind(scanner::token_kind::SYMBOL, std::string(context) + ": invalid sorted-val list");
            symbol sym = curr_symbol();
            next();
            expr ty = parse_expr(context);
            expr l = lctx().mk_local_decl(sym, ty);
            bindings.push_back(l);
            check_curr_kind(scanner::token_kind::RIGHT_PAREN, std::string(context) + ": invalid sorted-val list");
            next();
        }
        check_curr_kind(scanner::token_kind::RIGHT_PAREN, std::string(context) + ": invalid sorted-val list");
        next();
    }


    expr parse_expr(char const * context) {
        // { LEFT_PAREN, RIGHT_PAREN, KEYWORD, SYMBOL, STRING, INT, FLOAT, BV };
        symbol sym;
        std::unordered_map<std::string, expr>::const_iterator it;
        buffer<expr> args;
        optional<local_decl> l;
        //optional<local_decl>

        switch (curr_kind()) {
        case scanner::token_kind::SYMBOL:
            sym = curr_symbol();
            next();
            it = g_theory_constant_symbols->find(sym);
            if (it != g_theory_constant_symbols->end())
                return it->second;
            else if (l = lctx().get_local_decl_from_user_name(sym))
                return l->mk_ref();
            else
                return mk_constant(sym);
            lean_unreachable();
            break;
        case scanner::token_kind::STRING:
            // TODO(dhs): strings
            throw_parser_exception("string literals not accepted in expressions yet");
            lean_unreachable();
            break;
        case scanner::token_kind::INT:
            // TODO(dhs): Lean's bv may want a Nat instead of an Int
            return mk_mpq_macro(curr_numeral_next(), mk_constant(get_int_name()));
        case scanner::token_kind::FLOAT:
            return mk_mpq_macro(curr_numeral_next(), mk_constant(get_real_name()));
        case scanner::token_kind::BV:
            // TODO(dhs): bit vectors
            // (Already getting the value in the scanner, just don't have a good Lean target yet)
            throw_parser_exception("bit-vector literals not accepted in expressions yet");
            lean_unreachable();
            break;
        case scanner::token_kind::LEFT_PAREN:
            next();
            if (curr_kind() == scanner::token_kind::SYMBOL && curr_symbol() == g_symbol_dependent_type) {
                next();
                parse_exprs(args, context);
                return pre_elaborate_app(args);
            } else if (curr_kind() == scanner::token_kind::SYMBOL && curr_symbol() == g_token_forall) {
                next();
                buffer<expr> bindings;
                parse_sorted_var_list(bindings, context);
                expr e = parse_expr(context);
                expr pi = mk_binding(binding_type::FORALL, bindings, e);
                for (expr const & binding : bindings)
                    m_lctx.pop_local_decl();
                check_curr_kind(scanner::token_kind::RIGHT_PAREN, "invalid constant declaration, ')' expected");
                next();
                return pi;
            } else if (curr_kind() == scanner::token_kind::SYMBOL && curr_symbol() == g_token_exists) {
                throw_parser_exception("exists not accepted in expressions yet");
                lean_unreachable();
                /*
                next();
                buffer<expr> bindings;
                parse_sorted_var_list(context);
                expr e = parse_expr(context);
                // TODO(dhs): write this
                return Exists(bindings, e);
                */
            } else if (curr_kind() == scanner::token_kind::SYMBOL && curr_symbol() == g_token_let) {
                throw_parser_exception("let not accepted in expressions yet");
                lean_unreachable();
                /*
                next();
                buffer<expr> bindings;
                // TODO(dhs): write this
                parse_var_binding_list(context);
                expr e = parse_expr(context);
                // TODO(dhs): write this
                return Let(bindings, e);*/
            } else {
                parse_exprs(args, context);
                return pre_elaborate_app(args);
            }
        default:
            throw_parser_exception((std::string(context) + ", invalid sort").c_str());
            lean_unreachable();
            break;
        }
        lean_unreachable();
    }

    void parse_exprs(buffer<expr> & es, char const * context) {
        while (curr_kind() != scanner::token_kind::RIGHT_PAREN) {
            es.push_back(parse_expr(context));
        }
        if (es.empty()) {
            throw_parser_exception(std::string(context) + ", () not a legal expression");
        }
        next();
    }

    void parse_expr_list(buffer<expr> & es, char const * context) {
        check_curr_kind(scanner::token_kind::LEFT_PAREN, context);
        next();
        parse_exprs(es, context);
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
                    throw_parser_exception("invalid command, '(' expected");
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
        std::string const & s = m_scanner.get_str_val();
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
        else throw_parser_exception(std::string("unknown command: ") + s, pinfo);
    }

    // Individual commands
    void parse_assert() {
        lean_assert(curr_kind() == scanner::token_kind::SYMBOL);
        lean_assert(curr_symbol() == g_token_assert);
        next();

        expr e = parse_expr("invalid assert command");
        register_hypothesis(e);

        check_curr_kind(scanner::token_kind::RIGHT_PAREN, "invalid constant declaration, ')' expected");
        next();
    }

    void parse_check_sat() {
        lean_assert(curr_kind() == scanner::token_kind::SYMBOL);
        lean_assert(curr_symbol() == g_token_check_sat);
        next();

        metavar_context mctx;
        expr goal_mvar = mctx.mk_metavar_decl(lctx(), mk_constant(get_false_name()));
        vm_obj s = to_obj(tactic_state(env(), ios().get_options(), mctx, list<expr>(goal_mvar), goal_mvar));
        vm_obj result = get_tactic_vm_state(env()).invoke(*g_smt2_tactic, s);
        if (optional<tactic_state> s_new = is_tactic_success(result)) {
            mctx = s_new->mctx();
            expr proof = mctx.instantiate_mvars(goal_mvar);
            if (has_expr_metavar(proof)) {
                ios().get_regular_stream() << "<tactic succeeded but left metavars>\n";
            } else {
                ios().get_regular_stream() << "unsat\n";
            }
        } else {
            ios().get_regular_stream() << "<tactic failed>\n";
        }
        check_curr_kind(scanner::token_kind::RIGHT_PAREN, "invalid constant declaration, ')' expected");
        next();
    }

    void parse_check_sat_assuming() { throw_parser_exception("check-sat-assuming not yet supported"); }
    void parse_declare_const() {
        lean_assert(curr_kind() == scanner::token_kind::SYMBOL);
        lean_assert(curr_symbol() == g_token_declare_const);
        next();
        check_curr_kind(scanner::token_kind::SYMBOL, "invalid constant declaration, symbol expected");
        name c_name = name(curr_symbol());
        next();
        expr ty = parse_expr("invalid constant declaration");
        register_hypothesis(c_name, ty);
        check_curr_kind(scanner::token_kind::RIGHT_PAREN, "invalid constant declaration, ')' expected");
        next();
    }

    void parse_declare_fun() {
        lean_assert(curr_kind() == scanner::token_kind::SYMBOL);
        lean_assert(curr_symbol() == g_token_declare_fun);
        next();
        check_curr_kind(scanner::token_kind::SYMBOL, "invalid function declaration, symbol expected");
        name fn_name = name(curr_symbol());
        next();

        buffer<expr> parameter_sorts;
        parse_expr_list(parameter_sorts, "invalid function declaration");
        expr ty = parse_expr("invalid function declaration");
        for (int i = parameter_sorts.size() - 1; i >= 0; ++i) {
            ty = mk_arrow(parameter_sorts[i], ty);
        }
        register_hypothesis(fn_name, ty);
        check_curr_kind(scanner::token_kind::RIGHT_PAREN, "invalid function declaration, ')' expected");
        next();
    }

    void parse_declare_sort() {
        lean_assert(curr_kind() == scanner::token_kind::SYMBOL);
        lean_assert(curr_symbol() == g_token_declare_sort);
        next();

        check_curr_kind(scanner::token_kind::SYMBOL, "invalid sort declaration, symbol expected");
        name sort_name = name(curr_symbol());
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
        register_hypothesis(sort_name, ty);
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

    void parse_set_option() {
        lean_assert(curr_kind() == scanner::token_kind::SYMBOL);
        lean_assert(curr_symbol() == g_token_set_option);
        next();
        check_curr_kind(scanner::token_kind::KEYWORD, "invalid set-option command, keyword expected");
        symbol sym = curr_symbol();
        next();
        if (sym == g_token_use_locals) {
            m_use_locals = true;
        } else {
            // TODO(dhs): just a warning?
            throw_parser_exception(std::string("unsupported option: ") + sym);
        }
        check_curr_kind(scanner::token_kind::RIGHT_PAREN, "invalid set-option, ')' expected");
        next();
    }

public:

    // Constructor
    parser(environment const & env, io_state & ios, std::istream & strm, char const * strm_name, bool use_exceptions):
        m_env(env), m_ios(ios), m_scanner(strm, strm_name), m_use_exceptions(use_exceptions) {}

    // Entry point
    bool operator()() {
        parse_commands();
        return true;
    }
};

// Setup and teardown

void initialize_parser() {
    g_smt2_prefix = new name(name::mk_internal_unique_name());
    // TODO(dhs): write a theorem prover and call that instead
    g_smt2_tactic = new name({"tactic", "trace_state"});

    g_theory_constant_symbols = new std::unordered_map<std::string, expr>({
            // Sorts
            {"Bool", mk_Prop()},
            {"Int", mk_constant(get_int_name())},
            {"Real", mk_constant(get_real_name())},
            {"Array", mk_constant(get_array_name())},

            // (a) Core
            {"true", mk_constant(get_true_name())},
            {"false", mk_constant(get_false_name())},
                });

    g_theory_function_symbols = new std::unordered_map<std::string, fun_decl>({
            // TODO(dhs): other universe levels
            // Sorts
            {"BitVec", fun_decl(mk_constant(get_bv_name()), fun_attr::DEFAULT)},

            // I. Non-polymorphic
            // (a) Core
            {"not", fun_decl(mk_constant(get_not_name()), fun_attr::DEFAULT)},
            {"=>", fun_decl(mk_constant(get_implies_name()), fun_attr::RIGHT_ASSOC)},
            {"and", fun_decl(mk_constant(get_and_name()), fun_attr::LEFT_ASSOC)},
            {"or", fun_decl(mk_constant(get_or_name()), fun_attr::LEFT_ASSOC)},
            {"xor", fun_decl(mk_constant(get_xor_name()), fun_attr::LEFT_ASSOC)},

            // (b) Arithmetic
            {"div", fun_decl(mk_constant(get_div_name(), {mk_level_one()}), fun_attr::LEFT_ASSOC)},
            {"mod", fun_decl(mk_constant(get_mod_name()), fun_attr::DEFAULT)},
            {"abs", fun_decl(mk_constant(get_abs_name()), fun_attr::DEFAULT)},
            {"/", fun_decl(mk_constant(get_div_name(), {mk_level_one()}), fun_attr::LEFT_ASSOC)},
            {"to_real", fun_decl(mk_constant(get_real_of_int_name()), fun_attr::DEFAULT)},
            {"to_int", fun_decl(mk_constant(get_real_to_int_name()), fun_attr::DEFAULT)},
            {"is_int", fun_decl(mk_constant(get_real_is_int_name()), fun_attr::DEFAULT)},

             // (c) Arrays
            {"select", fun_decl(mk_constant(get_array_select_name()), fun_attr::DEFAULT)}, // TODO(dhs): may not exist yet
            {"store", fun_decl(mk_constant(get_array_store_name()), fun_attr::DEFAULT)}, // TODO(dhs): may not exist yet

            // II. Polymorphic
            // (a) Core
            {"=", fun_decl(mk_constant(get_eq_name(), {mk_level_one()}), fun_attr::CHAINABLE)},
            {"distinct", fun_decl(mk_constant(get_distinct_name()), fun_attr::PAIRWISE)},
            {"ite", fun_decl(mk_constant(get_ite_name()), fun_attr::DEFAULT)},

            // (b) Arithmetic
                {"+", fun_decl(mk_constant(get_add_name(), {mk_level_one()}), fun_attr::LEFT_ASSOC)},
            {"-", fun_decl(mk_constant(get_sub_name(), {mk_level_one()}), fun_attr::LEFT_ASSOC)}, // note: if 1 arg, then neg instead
            {"*", fun_decl(mk_constant(get_mul_name(), {mk_level_one()}), fun_attr::LEFT_ASSOC)},
            {"<", fun_decl(mk_constant(get_lt_name(), {mk_level_one()}), fun_attr::CHAINABLE)},
            {"<=", fun_decl(mk_constant(get_le_name(), {mk_level_one()}), fun_attr::CHAINABLE)},
            {">", fun_decl(mk_constant(get_gt_name(), {mk_level_one()}), fun_attr::CHAINABLE)},
            {">=", fun_decl(mk_constant(get_ge_name(), {mk_level_one()}), fun_attr::CHAINABLE)}
        });
}

void finalize_parser() {
    delete g_theory_constant_symbols;
    delete g_theory_function_symbols;

    delete g_smt2_prefix;
    delete g_smt2_tactic;
}

// Entry point
bool parse_commands(environment & env, io_state & ios, char const * fname, bool use_exceptions) {
    std::ifstream in(fname);
    if (in.bad() || in.fail())
        throw exception(sstream() << "failed to open file '" << fname << "'");

    buffer<module_name> olean_files;
    std::string base = dirname(fname);
    name f("init");
    optional<unsigned> k;
    olean_files.push_back(module_name(k, f));

    unsigned num_threads = 0;
    bool keep_imported_theorems = false;

    environment new_env = import_modules(env, base, olean_files.size(), olean_files.data(), num_threads, keep_imported_theorems, ios);
    parser p(new_env, ios, in, fname, use_exceptions);
    return p();
}

}}
