/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "kernel/environment.h"
#include "frontends/lean/type_util.h"
#include "library/inductive_compiler/ginductive.h"

namespace lean {

class mutual_decl_aux {
    buffer<expr> m_index_types;
    expr         m_full_index_type;
    buffer<expr> m_makers;
    buffer<expr> m_putters;
public:
    mutual_decl_aux(buffer<expr> const & index_types, expr const & full_index_type,
                    buffer<expr> const & makers, buffer<expr> const & putters):
        m_index_types(index_types), m_full_index_type(full_index_type),
        m_makers(makers), m_putters(putters) {}

    buffer<expr> const & get_index_types() const { return m_index_types; }
    expr const & get_full_index_type() const { return m_full_index_type; }
    buffer<expr> const & get_makers() const { return m_makers; }
    buffer<expr> const & get_putters() const { return m_putters; }
};

pair<ginductive_decl, mutual_decl_aux> compile_mutual_to_basic(environment const & env, ginductive_decl const & mut_decl);

environment post_process_mutual(environment const & env, options const & opts, name_map<implicit_infer_kind> const & implicit_infer_map,
                                ginductive_decl const & mut_decl, ginductive_decl const & basic_decl, mutual_decl_aux const & mut_aux);

void initialize_inductive_compiler_mutual();
void finalize_inductive_compiler_mutual();

}
