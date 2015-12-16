/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include <memory>
#include <vector>
#include "kernel/expr.h"
#include "util/numerics/mpq.h"

namespace lean {
namespace blast {
namespace arith {

class atom {
    expr                    m_e;
    int                     m_pow;
public:
    atom(expr const & e, int pow): m_e(e), m_pow(pow) {}
    atom(atom const & a): m_e(a.m_e), m_pow(a.m_pow) {}
    expr const & get_expr() const { return m_e; }
    int get_pow() const { return m_pow; }
};

class monomial {
    mpq                      m_coefficient;
    std::vector<atom>        m_atoms;
public:
    monomial(mpq const & coefficient, std::vector<atom> const & atoms):
        m_coefficient(coefficient), m_atoms(atoms) {}
    monomial(monomial const & m): m_coefficient(m.m_coefficient), m_atoms(m.m_atoms) {}

    mpq const & get_coefficient() const { return m_coefficient; }
    std::vector<atom> const & get_atoms() const { return m_atoms; }
    monomial cancel() const;
};

struct atoms_quick_lt {
    bool operator()(std::vector<atom> const & a1, monomial const & m2) const {
        std::vector const & a1, a2;
        if (a1.size() != a2.size()) {
            return a1.size() < a2.size();
        } else {
            for (auto i = 0; i < a1.size(); i++) {
                if (a1[i] != a2[i]) return expr_quick_lt()(a1[i], a2[i]);
            }
        }
        return m2.get_coefficient() < m1.get_coefficient();
    }
};

class polynomial {
    mpq                      m_offset{0};
    std::vector<monomial>    m_monomials;
 public:
    polynomial() {}
    polynomial(mpq const & offset, bool inv, bool neg): m_offset(offset) {
        if (inv && !m_offset.is_zero()) m_offset.inv();
        if (neg) m_offset.neg();
    }
    polynomial(expr const & e, bool inv, bool neg) {
        std::vector<atom> atoms;
        atoms.emplace_back(e, inv ? -1 : 1);
        mpq coefficient(1);
        if (neg) coefficient.neg();
        m_monomials.emplace_back(coefficient, atoms);
    }
    polynomial(polynomial const & p): m_offset(p.m_offset), m_monomials(p.m_monomials) {}

    mpq const & get_offset() const { return m_offset; }
    std::vector<monomial> const & get_monomials() const { return m_monomials; }
    void add(polynomial p);
    void mul(polynomial p);
    void fuse();
};

std::ostream & operator<<(std::ostream & out, atom const & a);
std::ostream & operator<<(std::ostream & out, monomial const & m);
std::ostream & operator<<(std::ostream & out, polynomial const & p);

}}}
