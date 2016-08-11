/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "kernel/environment.h"
#include "library/constants.h"
#include "library/inductive.h"
#include "library/util.h"
#include "frontends/lean/inductive/sizeof.h"

namespace lean {

static name * g_inductive_sizeof_v_name     = nullptr;
static name * g_inductive_sizeof_F_name     = nullptr;

static name const & v_name() { return *g_inductive_sizeof_v_name; }
static name const & F_name() { return *g_inductive_sizeof_F_name; }

class mk_basic_sizeof_fn {
private:
    type_context & m_tctx;
    name           m_ind_name;
    bool           m_is_recursive;

public:
    mk_basic_sizeof_fn(type_context & tctx, name const & ind_name):
        m_tctx(tctx), m_ind_name(ind_name), m_is_recursive(is_recursive_datatype(ind_name)) {}

    /* Our goal is to define a function with the following type:
       Pi A b, has_sizeof (ind_name A b). */
    environment operator()() {
        declaration d     = tctx.env().find(ind_name);

        // (1) Introduce locals for arguments to the inductive type
        // t = Pi A b, Type
        expr t = d.get_type();
        type_context::tmp_locals local_factory(m_tctx);

        while (is_pi(t)) {
            tctx.push_local_from_binding(t);
            t = binding_body(t);
        }

        // (2) Construct (not-yet-abstracted) type of definition
        // has_size_of (ind_name A b)
        expr ind_type = mk_app(m_tctx, ind_name, local_factory.as_buffer());
        expr goal_type = mk_app(m_tctx, get_has_sizeof_name(), ind_type);

        // (3) Introduce a local with type `ind_name`.
        // We need to compute a `nat` and then abstract.
        expr v = m_tctx.push_local(v_name(), ind_type);

        // (4) Create a metavar of type nat, that can depend on any of the locals we have created so far
        expr m_nat_pre = m_tctx.mk_metavar_decl(m_tctx.lctx(), mk_constant(get_nat_name()));

        // (5) If the datatype is recursive, we need a `below` hypothesis.
        list<expr> m_nats;
        if (m_is_recursive) {
            metavar_context mctx = m_tctx.mctx();
            m_nats = inductive(tctx.env(), tctx.get_options(), transparency_mode::Semireducible, mctx,
                              m_nat, v, name(ind_name, "brec_on"));
            m_tctx.set_mctx(mctx);
        } else {
            m_nats = list<expr>(m_nat);
        }
        lean_assert(length(m_nats) == 1);
        expr m_nat = head(m_nats);

        // (6) Intro

        // (6) apply cases
        pair<list<expr>, list<name> > cases_goals
        {
            metavar_context mctx = m_tctx.mctx();
            m_nats = cases(tctx.env(), tctx.get_options(), transparency_mode::Semireducible, mctx,
                           m_nat, v, name(ind_name, "brec_on"));
            m_tctx.set_mctx(mctx);
        }
        pair<list<expr>, list<name> > cases_goals = cases(m_tctx.env(), m_tctx.get_options(), transparency_mode::Semireducible, mctx,
pair<list<expr>, list<name>>
cases(environment const & env, options const & opts, transparency_mode const & m, metavar_context & mctx,
      expr const & mvar, expr const & H, list<name> & ids, intros_list * ilist, renaming_list * rlist);






list<expr> induction(environment const & env, options const & opts, transparency_mode const & m, metavar_context & mctx,
                     expr const & mvar, expr const & H, name const & rec_name, list<name> & ns,
                     intros_list * ilist, renaming_list * rlist);

        optional<expr> F;
        if (is_recursive_datatype(tctx.env(), ind_name))
            F = m_tctx.push_local(F_name(), mk_app(name(ind_name, "below"), v));

        // (5) We are going to use `cases_on`, so we need to compute a nat
        // for each constructor.
        list<name> ir_names = get_intro_rule_names(tctx.env(), m_ind_name);
        unsigned num_intro_rules = length(ir_names);

        buffer<expr> cases;
        for (name const & ir_name : ir_names)
            cases.push_back(construct_size_for_case(ir_name));





        //
        bool is_recursive = is_recursive_datatype(tctx.env(), ind_name);
        if (is_recursive) {
            throw exception("no support for recursive types yet");
        } else {


        }






           then intro `_v >>= (λ x, induction_core semireducible x (I_name <.> "brec_on") [v_name, F_name])



   then intro `_v >>= (λ x, induction_core semireducible x (I_name <.> "brec_on") [v_name, F_name])

    }

}


environment mk_basic_sizeof(type_context & tctx, name const & ind_name) {
    return mk_basic_sizeof_fn(tctx, ind_name)();
}





}

environment mk_derived_sizeof(environment const & env, name const & ind_name) {
    throw exception("TODO(dhs): implement");
}

environment mk_has_sizeof(environment const & env, name const & ind_name) {
    throw exception("TODO(dhs): implement");
}

environment mk_basic_sizeof_spec_lemmas(environment const & env, name const & ind_name) {
    throw exception("TODO(dhs): implement");
}

environment mk_derived_sizeof_spec_lemmas(environment const & env, name const & ind_name) {
     throw exception("TODO(dhs): implement");
}

void initialize_inductive_sizeof() {
    g_inductive_sizeof_v_name = new name{"_v"};
    g_inductive_sizeof_F_name = new name{"_F"};
}

void finalize_inductive_sizeof() {
    delete g_inductive_sizeof_v_name;
    delete g_inductive_sizeof_F_name;
}
}
