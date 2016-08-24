/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include <utility>
#include <string>
#include "kernel/environment.h"
#include "library/ginductive.h"
#include "library/module.h"
#include "library/kernel_serializer.h"

namespace lean {

// TODO(dhs): evidence is piling up that it is a mistake to store buffers
// in the ginductive_decls

serializer & operator<<(serializer & s, ginductive_decl const & decl) {
    write_list<name>(s, to_list(decl.get_lp_names()));
    write_list<expr>(s, to_list(decl.get_params()));
    write_list<expr>(s, to_list(decl.get_inds()));
    for (buffer<expr> const & irs : decl.get_intro_rules()) {
        write_list<expr>(s, to_list(irs));
    }
    return s;
}

ginductive_decl read_ginductive_decl(deserializer & d) {
    ginductive_decl decl;
    list<name> lp_names = read_list<name>(d, read_name);
    list<expr> params   = read_list<expr>(d, read_expr);
    list<expr> inds     = read_list<expr>(d, read_expr);

    unsigned num_inds = length(inds);
    for (unsigned i = 0; i < num_inds; ++i) {
        list<expr> irs = read_list<expr>(d, read_expr);
        decl.get_intro_rules().emplace_back();
        to_buffer(irs, decl.get_intro_rules().back());
    }
    to_buffer(lp_names, decl.get_lp_names());
    to_buffer(params, decl.get_params());
    to_buffer(inds, decl.get_inds());
    return decl;
}

inline deserializer & operator>>(deserializer & d, ginductive_decl & decl) {
    decl = read_ginductive_decl(d);
    return d;
}

static name * g_ginductive_extension = nullptr;
static std::string * g_ginductive_key = nullptr;

struct ginductive_env_ext : public environment_extension {
    name_map<list<name> > m_ind_to_irs;
    name_map<name>        m_ir_to_ind;
    name_map<unsigned>    m_num_params;

    ginductive_env_ext() {}

    void register_ginductive_decl(ginductive_decl const & decl) {
        for (unsigned i = 0; i < decl.get_inds().size(); ++i) {
            name const & ind_name = mlocal_name(decl.get_inds()[i]);
            buffer<name> ir_names;
            for (expr const & ir : decl.get_intro_rules()[i]) {
                name ir_name = mlocal_name(ir);
                ir_names.push_back(ir_name);
                m_ir_to_ind.insert(ir_name, ind_name);
            }
            m_ind_to_irs.insert(ind_name, to_list(ir_names));
            m_num_params.insert(ind_name, decl.get_params().size());
        }
    }

    bool is_ginductive(name const & ind_name) const {
        return m_ind_to_irs.contains(ind_name);
    }

    optional<list<name> > get_intro_rules(name const & ind_name) const {
        list<name> const * ir_names = m_ind_to_irs.find(ind_name);
        if (ir_names)
            return optional<list<name> >(*ir_names);
        else
            return optional<list<name> >();
    }

    optional<name> is_intro_rule(name const & ir_name) const {
        name const * ind_name = m_ir_to_ind.find(ir_name);
        if (ind_name)
            return optional<name>(*ind_name);
        else
            return optional<name>();
    }

    unsigned get_num_params(name const & ind_name) const {
        unsigned const * num_params = m_num_params.find(ind_name);
        lean_assert(num_params);
        return *num_params;
    }
};

struct ginductive_env_ext_reg {
    unsigned m_ext_id;
    ginductive_env_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<ginductive_env_ext>()); }
};

static ginductive_env_ext_reg * g_ext = nullptr;

static ginductive_env_ext const & get_extension(environment const & env) {
    return static_cast<ginductive_env_ext const &>(env.get_extension(g_ext->m_ext_id));
}

static environment update(environment const & env, ginductive_env_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<ginductive_env_ext>(ext));
}

environment register_ginductive_decl(environment const & env, ginductive_decl const & decl) {
    ginductive_env_ext ext(get_extension(env));
    ext.register_ginductive_decl(decl);
    environment new_env = update(env, ext);
    return module::add(new_env, *g_ginductive_key, [=](environment const &, serializer & s) { s << decl; });
}

bool is_ginductive(environment const & env, name const & ind_name) {
    return get_extension(env).is_ginductive(ind_name);
}

optional<list<name> > get_ginductive_intro_rules(environment const & env, name const & ind_name) {
    return get_extension(env).get_intro_rules(ind_name);
}

optional<name> is_ginductive_intro_rule(environment const & env, name const & ir_name) {
    return get_extension(env).is_intro_rule(ir_name);
}

unsigned get_ginductive_num_params(environment const & env, name const & ind_name) {
    return get_extension(env).get_num_params(ind_name);
}

/* For basic inductive types, we can prove this lemma using <ind_name>.no_confusion.

   For non-basic inductive types, we first create a function <ind_name>.cidx that maps
   each element of \e ind_type to a natural number depending only on its constructor.
   We then prove the lemma <tt>forall c1 c2, cidx c1 != cidx c2 -> c1 != c2</tt> and
   use it to prove the desired theorem.
*/
expr prove_intro_rules_disjoint(environment const & env, name const & ir_name1, name const & ir_name2) {
    throw exception("TODO(dhs): implement");
}

static void ginductive_reader(deserializer & d, shared_environment & senv,
                              std::function<void(asynch_update_fn const &)> &,
                              std::function<void(delayed_update_fn const &)> &) {
    ginductive_decl decl;
    d >> decl;
    senv.update([=](environment const & env) -> environment {
            ginductive_env_ext ext = get_extension(env);
            ext.register_ginductive_decl(decl);
            return update(env, ext);
        });
}


void initialize_library_ginductive() {
    g_ginductive_extension = new name("ginductive_extension");
    g_ginductive_key       = new std::string("gind");
    g_ext                  = new ginductive_env_ext_reg();

    register_module_object_reader(*g_ginductive_key, ginductive_reader);
}

void finalize_library_ginductive() {
    delete g_ginductive_extension;
    delete g_ginductive_key;
    delete g_ext;
}
}
