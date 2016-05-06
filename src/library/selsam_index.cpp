/*
Copyright (c) 2016 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "kernel/for_each_fn.h"
#include "kernel/find_fn.h"
#include "library/selsam_index.h"
#include "library/trace.h"
#include "util/optional.h"
#include <set>
#include <algorithm>

namespace lean {

static name * g_selsam_index_prefix = nullptr;
LEAN_THREAD_VALUE(unsigned, g_next_selsam_index, 0);

static unsigned next_selsam_index() {
    unsigned r = g_next_selsam_index;
    g_next_selsam_index++;
    return r;
}

optional<unsigned> is_selsam_local(name const & n) {
    if (!n.is_atomic() && !n.get_prefix().is_atomic() && n.get_prefix().get_prefix() == *g_selsam_index_prefix)
        return optional<unsigned>(n.get_numeral());
    else
        return optional<unsigned>();
 }

optional<unsigned> is_selsam_local(expr const & e) {
    if (is_local(e))
        return is_selsam_local(mlocal_name(e));
    else
        return optional<unsigned>();
}

name mk_selsam_local_name(unsigned idx) {
    name n = name(name(*g_selsam_index_prefix, next_selsam_index()), idx);
    return n;
}

expr mk_selsam_local(expr const & type) {
    name n = mk_selsam_local_name(0);
    lean_trace(name({"cc", "lambda"}), tout() << "New Selsam local: " << n << " : " << (is_local(type) ? mlocal_name(type) : name()) << " | " << type << "\n";);
    return mk_local(n, type);
}

bool has_selsam_local(expr const & e) {
    optional<expr> l = find(e, [&](expr const & t, unsigned) {
            return is_selsam_local(t);
        });
    if (l)
        return true;
    else
        return false;
}

expr lift_local(expr const & e) {
    auto old_idx = is_selsam_local(e);
    lean_assert(old_idx);
    lean_assert(!mlocal_name(e).is_atomic());
    name lifted_name = name(mlocal_name(e).get_prefix(), *old_idx+1);
    return mk_local(lifted_name, lifted_name, mlocal_type(e), local_info(e), e.get_tag());
}

expr lower_local(expr const & e) {
    auto old_idx = is_selsam_local(e);
    lean_assert(old_idx);
    lean_assert(!mlocal_name(e).is_atomic());
    lean_assert(*old_idx > 0);
    name lowered_name = name(mlocal_name(e).get_prefix(), *old_idx - 1);
    return mk_local(lowered_name, lowered_name, mlocal_type(e), local_info(e), e.get_tag());
}

// TODO(dhs): cache
expr map_selsam_locals(expr const & e, bool lift) {
    if (!has_local(e))
        return e;

    switch (e.kind()) {
    case expr_kind::Constant: case expr_kind::Sort: case expr_kind::Var: {
        lean_unreachable();
    }
    case expr_kind::Meta:     case expr_kind::Local: {
        expr new_ty = map_selsam_locals(mlocal_type(e), lift);
        expr new_e = update_mlocal(e, new_ty);
        if (is_selsam_local(new_e)) {
            expr new_new_e = (lift ? lift_local(new_e) : lower_local(new_e));
            lean_trace(name({"cc", "lambda"}), tout() << (lift ? "lifting: " : "lowering: ") << new_e << " ==> " << new_new_e << "\n";);
            new_e = new_new_e;
        }
        return new_e;
    }
    case expr_kind::App: {
        expr new_f = map_selsam_locals(app_fn(e), lift);
        expr new_a = map_selsam_locals(app_arg(e), lift);
        return update_app(e, new_f, new_a);
    }
    case expr_kind::Pi: case expr_kind::Lambda: {
        expr new_d = map_selsam_locals(binding_domain(e), lift);
        expr new_b = map_selsam_locals(binding_body(e), lift);
        return update_binding(e, new_d, new_b);
    }
    case expr_kind::Let: {
        expr new_t = map_selsam_locals(let_type(e), lift);
        expr new_v = map_selsam_locals(let_value(e), lift);
        expr new_b = map_selsam_locals(let_body(e), lift);
        return update_let(e, new_t, new_v, new_b);
    }
    case expr_kind::Macro: {
        buffer<expr> new_args;
        unsigned nargs = macro_num_args(e);
        for (unsigned i = 0; i < nargs; i++)
            new_args.push_back(map_selsam_locals(macro_arg(e, i), lift));
        return update_macro(e, new_args.size(), new_args.data());
    }}
    lean_unreachable();
}

expr lift_selsam_locals(expr const & e) {
    expr r = map_selsam_locals(e, true);
    lean_trace(name({"cc", "lambda"}), tout() << "LIFT:\n " << e << "\n==>\n" << r << "\n";);
    return r;
}
expr lower_selsam_locals(expr const & e) {
    expr r = map_selsam_locals(e, false);
    lean_trace(name({"cc", "lambda"}), tout() << "LOWER:\n " << e << "\n==>\n" << r << "\n";);
    return r;
}

expr_struct_set all_locals_at_selsam_index0(expr const & e) {
    expr_struct_set slocals;
    for_each(e, [&](expr const & t, unsigned) {
            if (auto idx = is_selsam_local(t)) {
                if (*idx == 0) {
                    slocals.insert(t);
                }
            }
            return true;
        });
    return slocals;
}

unsigned get_selsam_local_unique_id(name const & n) {
    return n.get_prefix().get_numeral();
}

bool selsam_local_eq_upto_index(expr const & e1, expr const & e2) {
    lean_assert(is_selsam_local(e1) && is_selsam_local(e2));
    return get_selsam_local_unique_id(mlocal_name(e1)) == get_selsam_local_unique_id(mlocal_name(e2));
}

void initialize_selsam_index() {
    g_selsam_index_prefix = new name(name::mk_internal_unique_name());
}

void finalize_selsam_index() {
    delete g_selsam_index_prefix;
}

}
