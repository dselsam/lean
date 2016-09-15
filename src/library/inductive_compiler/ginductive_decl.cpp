/*
  Copyright (c) 2016 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Daniel Selsam
*/
#include "library/inductive_compiler/ginductive_decl.h"
#include "library/util.h"

namespace lean {

bool ginductive_decl::is_ind(expr const & e) const {
    return is_constant(e)
        && std::any_of(m_inds.begin(), m_inds.end(), [&](expr const & ind) {
                return const_name(e) == mlocal_name(ind);
            });
}


bool ginductive_decl::has_ind_occ(expr const & t) const {
    return static_cast<bool>(find(t, [&](expr const & e, unsigned) { return is_ind(e); }));
}

bool ginductive_decl::is_ind_app(expr const & e, unsigned ind_idx, buffer<expr> & indices) const {
    buffer<expr> args;
    expr fn = get_app_args(e, args);
    if (!is_ind(fn, ind_idx))
        return false;
    lean_assert(args.size() >= m_params.size());
    for (unsigned i = m_params.size(); i < args.size(); ++i) {
        indices.push_back(args[i]);
    }
    return true;
}

bool ginductive_decl::is_ind_app(expr const & e, buffer<expr> & indices) const {
    buffer<expr> args;
    expr fn = get_app_args(e, args);
    if (!is_ind(fn))
        return false;
    lean_assert(args.size() >= m_params.size());
    for (unsigned i = m_params.size(); i < args.size(); ++i) {
        indices.push_back(args[i]);
    }
    return true;
}

bool ginductive_decl::is_ir(expr const & e, unsigned ind_idx) const {
    return is_constant(e)
        && std::any_of(m_intro_rules[ind_idx].begin(), m_intro_rules[ind_idx].end(), [&](expr const & ir) {
                return const_name(e) == mlocal_name(ir);
            });
}

bool ginductive_decl::is_ir(expr const & e) const {
    if (!is_constant(e))
        return false;
    for (unsigned ind_idx = 0; ind_idx < m_inds.size(); ++ind_idx) {
        if (is_ir(e, ind_idx))
            return true;
    }
    return false;
}

void ginductive_decl::args_to_indices(buffer<expr> const & args, buffer<expr> & indices) const {
    for (unsigned i = get_num_params(); i < args.size(); ++i)
        indices.push_back(args[i]);
}

expr ginductive_decl::get_app_indices(expr const & e, buffer<expr> & indices) const {
    buffer<expr> args;
    expr fn = get_app_args(e, args);
    lean_assert(is_ind(fn));
    lean_assert(args.size() >= m_params.size());
    for (unsigned i = m_params.size(); i < args.size(); ++i) {
        indices.push_back(args[i]);
    }
    return fn;
}

bool ginductive_decl::is_param(expr const & e) const {
    return is_local(e)
        && std::any_of(m_params.begin(), m_params.end(), [&](expr const & param) { return e == param; });
}

level ginductive_decl::get_result_level() const {
    return get_datatype_level(mlocal_type(m_inds[0]));
}

}
