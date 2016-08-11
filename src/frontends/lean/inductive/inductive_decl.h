/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "kernel/environment.h"
#include "kernel/inductive/inductive.h"

namespace lean {

class generalized_inductive_decl {
    list<expr>                      m_params;
    level_param_names               m_lp_names;
    list<inductive::inductive_decl> m_ind_decls;

public:
    generalized_inductive_decl(list<expr> const & params,
                               level_param_names const & lp_names,
                               list<inductive_decl> const & ind_decl):
        m_params(params), m_lp_names(lp_names), m_ind_decls(ind_decls) {}
    unsigned get_num_params() const { return m_num_params; }
    level_param_names get_lp_names() const { return m_lp_names; }
    list<inductive::inductive_decl> get_inductive_decls() const { return m_ind_decls; }
};

typedef generalized_inductive_decl basic_inductive_decl;
typedef generalized_inductive_decl mutual_inductive_decl;

}
