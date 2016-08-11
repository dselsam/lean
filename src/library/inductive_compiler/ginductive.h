/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include "kernel/environment.h"
#include "kernel/inductive/inductive.h"

namespace lean {

/* \remark "g" is for "generalized" */
class ginductive_decl {
    list<expr>                      m_params;
    level_param_names               m_lp_names;
    list<inductive::inductive_decl> m_decls;
public:
    ginductive_decl(list<expr> const & params,
                    level_param_names const & lp_names,
                    list<inductive_decl> const & decls):
        m_params(params), m_lp_names(lp_names), m_decls(decls) {}
    unsigned get_num_params() const { return m_num_params; }
    level_param_names get_lp_names() const { return m_lp_names; }
    list<inductive::inductive_decl> get_inductive_decls() const { return m_decls; }
};

/* \brief This procedure accepts "generalized" inductive declarations that may be
   mutually inductive and even nested, and compiles them into "basic" inductive
   types that can be recognized by the kernel. */
environment register_ginductive_decl(environment const & env, ginductive_decl const & gdecl);

void initialize_ginductive();
void finalize_ginductive();

}
