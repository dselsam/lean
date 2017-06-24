/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <limits>
#include <unordered_map>
#include <vector>
#include "util/name_hash_map.h"
#include "kernel/free_vars.h"
#include "kernel/replace_fn.h"
#include "kernel/declaration.h"
#include "kernel/instantiate.h"

namespace lean {

struct iuniv_key {
    name m_n;
    levels m_ls;
    unsigned m_hash;
    iuniv_key(name const & n, levels const & ls): m_n(n), m_ls(ls) {
        m_hash = n.hash(); // + 17 * hash(ls);
    }
};

struct iuniv_key_hash_fn {
    unsigned operator()(iuniv_key const & k) const { return k.m_hash; }
};

struct iuniv_key_eq_fn {
    bool operator()(iuniv_key const & k1, iuniv_key const & k2) const {
        return k1.m_n == k2.m_n && k1.m_ls == k2.m_ls;
    }
};

struct iuniv_val {
    declaration m_decl;
    levels m_ls;
    expr m_e;

    iuniv_val(declaration const & decl, levels const & ls, expr const & e):
        m_decl(decl), m_ls(ls), m_e(e) {}
};

class instantiate_univ_cache {
    std::unordered_map<iuniv_key, iuniv_val, iuniv_key_hash_fn, iuniv_key_eq_fn> m_cache;

public:
    optional<expr> is_cached(declaration const & d, levels const & ls) {
        auto r = m_cache.find({d.get_name(), ls});
        if (r != m_cache.end()) {
            return some_expr(r->second.m_e);
        } else {
            return none_expr();
        }
    }

    void save(declaration const & d, levels const & ls, expr const & r) {
        m_cache.insert({{d.get_name(), ls}, {d, ls, r}});
    }

    void clear() {
        m_cache.clear();
    }
};

template<bool rev>
struct instantiate_easy_fn {
    unsigned n;
    expr const * subst;
    instantiate_easy_fn(unsigned _n, expr const * _subst):n(_n), subst(_subst) {}
    optional<expr> operator()(expr const & a, bool app) const {
        if (closed(a))
            return some_expr(a);
        if (is_var(a) && var_idx(a) < n)
            return some_expr(subst[rev ? n - var_idx(a) - 1 : var_idx(a)]);
        if (app && is_app(a))
        if (auto new_a = operator()(app_arg(a), false))
        if (auto new_f = operator()(app_fn(a), true))
            return some_expr(mk_app(*new_f, *new_a, a.get_tag()));
        return none_expr();
    }
};

expr instantiate(expr const & a, unsigned s, unsigned n, expr const * subst) {
    if (
#ifndef LEAN_NO_FREE_VAR_RANGE_OPT
        s >= get_free_var_range(a) ||
#endif
        n == 0)
        return a;
    if (s == 0)
        if (auto r = instantiate_easy_fn<false>(n, subst)(a, true))
            return *r;
    return replace(a, [=](expr const & m, unsigned offset) -> optional<expr> {
            unsigned s1 = s + offset;
            if (s1 < s)
                return some_expr(m); // overflow, vidx can't be >= max unsigned
#ifndef LEAN_NO_FREE_VAR_RANGE_OPT
            if (s1 >= get_free_var_range(m))
                return some_expr(m); // expression m does not contain free variables with idx >= s1
#endif
            if (is_var(m)) {
                unsigned vidx = var_idx(m);
                if (vidx >= s1) {
                    unsigned h = s1 + n;
                    if (h < s1 /* overflow, h is bigger than any vidx */ || vidx < h) {
                        return some_expr(lift_free_vars(subst[vidx - s1], offset));
                    } else {
                        return some_expr(mk_var(vidx - n));
                    }
                }
            }
            return none_expr();
        });
}

expr instantiate(expr const & e, unsigned n, expr const * s) { return instantiate(e, 0, n, s); }
expr instantiate(expr const & e, std::initializer_list<expr> const & l) {  return instantiate(e, l.size(), l.begin()); }
expr instantiate(expr const & e, unsigned i, expr const & s) { return instantiate(e, i, 1, &s); }
expr instantiate(expr const & e, expr const & s) { return instantiate(e, 0, s); }

expr instantiate_rev(expr const & a, unsigned n, expr const * subst) {
    if (closed(a))
        return a;
    if (auto r = instantiate_easy_fn<true>(n, subst)(a, true))
        return *r;
    return replace(a, [=](expr const & m, unsigned offset) -> optional<expr> {
#ifndef LEAN_NO_FREE_VAR_RANGE_OPT
            if (offset >= get_free_var_range(m))
                return some_expr(m); // expression m does not contain free variables with idx >= offset
#endif
            if (is_var(m)) {
                unsigned vidx = var_idx(m);
                if (vidx >= offset) {
                    unsigned h = offset + n;
                    if (h < offset /* overflow, h is bigger than any vidx */ || vidx < h) {
                        return some_expr(lift_free_vars(subst[n - (vidx - offset) - 1], offset));
                    } else {
                        return some_expr(mk_var(vidx - n));
                    }
                }
            }
            return none_expr();
        });
}

bool is_head_beta(expr const & t) {
    return is_app(t) && is_lambda(get_app_fn(t));
}

expr apply_beta(expr f, unsigned num_args, expr const * args) {
    if (num_args == 0) {
        return f;
    } else if (!is_lambda(f)) {
        return mk_rev_app(f, num_args, args);
    } else {
        unsigned m = 1;
        while (is_lambda(binding_body(f)) && m < num_args) {
            f = binding_body(f);
            m++;
        }
        lean_assert(m <= num_args);
        return mk_rev_app(instantiate(binding_body(f), m, args + (num_args - m)), num_args - m, args);
    }
}

expr head_beta_reduce(expr const & t) {
    if (!is_head_beta(t)) {
        return t;
    } else {
        buffer<expr> args;
        expr const & f = get_app_rev_args(t, args);
        lean_assert(is_lambda(f));
        return head_beta_reduce(apply_beta(f, args.size(), args.data()));
    }
}

expr instantiate_univ_params(expr const & e, level_param_names const & ps, levels const & ls) {
    if (!has_param_univ(e))
        return e;
    return replace(e, [&](expr const & e) -> optional<expr> {
            if (!has_param_univ(e))
                return some_expr(e);
            if (is_constant(e)) {
                return some_expr(update_constant(e, map_reuse(const_levels(e),
                                                              [&](level const & l) { return instantiate(l, ps, ls); },
                                                              [](level const & l1, level const & l2) { return is_eqp(l1, l2); })));
            } else if (is_sort(e)) {
                return some_expr(update_sort(e, instantiate(sort_level(e), ps, ls)));
            } else {
                return none_expr();
            }
        });
}

MK_THREAD_LOCAL_GET(instantiate_univ_cache, get_type_univ_cache, );
MK_THREAD_LOCAL_GET(instantiate_univ_cache, get_value_univ_cache, );

expr instantiate_type_univ_params(declaration const & d, levels const & ls) {
    lean_assert(d.get_num_univ_params() == length(ls));
    if (is_nil(ls) || !has_param_univ(d.get_type()))
        return d.get_type();
    instantiate_univ_cache & cache = get_type_univ_cache();
    if (auto r = cache.is_cached(d, ls))
        return *r;
    expr r = instantiate_univ_params(d.get_type(), d.get_univ_params(), ls);
    cache.save(d, ls, r);
    return r;
}

expr instantiate_value_univ_params(declaration const & d, levels const & ls) {
    lean_assert(d.get_num_univ_params() == length(ls));
    if (is_nil(ls) || !has_param_univ(d.get_value()))
        return d.get_value();
    instantiate_univ_cache & cache = get_value_univ_cache();
    if (auto r = cache.is_cached(d, ls))
        return *r;
    expr r = instantiate_univ_params(d.get_value(), d.get_univ_params(), ls);
    cache.save(d, ls, r);
    return r;
}

void clear_instantiate_cache() {
    get_type_univ_cache().clear();
    get_value_univ_cache().clear();
}
}
