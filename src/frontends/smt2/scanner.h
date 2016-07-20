/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include <string>
#include <iostream>
#include "util/name.h"
#include "util/flet.h"
#include "util/numerics/mpq.h"
#include "kernel/environment.h"

namespace lean {
namespace smt2 {

class scanner {
public:
    enum class token_kind { END, LEFT_PAREN, RIGHT_PAREN, KEYWORD, SYMBOL, STRING, INT, FLOAT, BV };

    enum class char_kind { END, WHITESPACE, COMMENT, LEFT_PAREN, RIGHT_PAREN, KEYWORD, QUOTED_SYMBOL, STRING, NUMBER, BV, SIMPLE_SYMBOL, UNEXPECTED };

private:
    std::istream &      m_stream;
    std::string         m_stream_name;
    std::string         m_curr_line;
    bool                m_last_line;

    char                m_curr;  // current char;
    int                 m_cpos; // position of the char
    int                 m_cline; // line of the char

    token_kind          m_token_kind; // current token;
    int                 m_tpos;   // start position of the token
    int                 m_tline;  // line of the token

    std::string         m_str_val;
    name                m_name_val; // TODO(dhs): string here?
    mpq                 m_num_val;
    unsigned            m_bv_size;

    [[ noreturn ]] void throw_exception(char const * msg);

    void next();
    char curr() const { return m_curr; }
    char curr_next() { char c = curr(); next(); return c; }
    void check_not_eof(char const * error_msg);

    bool is_next_digit();
    void read_simple_symbol_core();
    void read_hex_bv_literal();
    void read_bin_bv_literal();

public:
    scanner(std::istream & strm, char const * strm_name = nullptr, unsigned line = 1);

    void read_simple_symbol();
    void read_keyword();
    void read_quoted_symbol();
    void read_comment();
    token_kind read_number();
    void read_string();
    void read_bv_literal();

    int get_line() const { return m_cline; }
    int get_pos() const { return m_cpos; }
    token_kind scan();

    mpq const & get_num_val() const { return m_num_val; }
    name const & get_name_val() const { return m_name_val; }
    std::string const & get_str_val() const { return m_str_val; }
    token_kind const & get_token_kind() const { return m_token_kind; }

    std::string const & get_stream_name() const { return m_stream_name; }

};

std::ostream & operator<<(std::ostream & out, scanner::token_kind k);
void initialize_scanner();
void finalize_scanner();
}}
