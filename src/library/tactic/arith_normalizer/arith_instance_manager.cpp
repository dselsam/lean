/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "library/constants.h"
#include "library/app_builder.h"
#include "library/num.h"
#include "library/util.h"
#include "library/tactic/arith_normalizer/arith_instance_manager.h"

namespace lean {

arith_instance_manager::arith_instance_manager(type_context & tctx, expr const & type):
    m_tctx(tctx), m_type(type) { m_level = get_level(m_tctx, type);}

arith_instance_manager::arith_instance_manager(type_context & tctx, expr const & type, level const & l):
    m_tctx(tctx), m_type(type), m_level(l) {}

bool arith_instance_manager::is_add_group() {
    if (m_is_add_group) {
        return *m_is_add_group;
    } else {
        expr inst_type = mk_app(mk_constant(get_add_group_name(), {m_level}), m_type);
        if (auto inst = m_tctx.mk_class_instance(inst_type)) {
            m_is_add_group = optional<bool>(true);
            return true;
        } else {
            m_is_add_group = optional<bool>(false);
            return false;
        }
    }
}

bool arith_instance_manager::is_comm_semiring() {
    if (m_is_comm_semiring) {
        return *m_is_comm_semiring;
    } else {
        expr inst_type = mk_app(mk_constant(get_comm_semiring_name(), {m_level}), m_type);
        if (auto inst = m_tctx.mk_class_instance(inst_type)) {
            m_is_comm_semiring = optional<bool>(true);
            return true;
        } else {
            m_is_comm_semiring = optional<bool>(false);
            return false;
        }
    }
}

bool arith_instance_manager::is_comm_ring() {
    if (m_is_comm_ring) {
        return *m_is_comm_ring;
    } else {
        expr inst_type = mk_app(mk_constant(get_comm_ring_name(), {m_level}), m_type);
        if (auto inst = m_tctx.mk_class_instance(inst_type)) {
            m_is_comm_ring = optional<bool>(true);
            return true;
        } else {
            m_is_comm_ring = optional<bool>(false);
            return false;
        }
    }
}

bool arith_instance_manager::is_linear_ordered_semiring() {
    if (m_is_linear_ordered_semiring) {
        return *m_is_linear_ordered_semiring;
    } else {
        expr inst_type = mk_app(mk_constant(get_linear_ordered_semiring_name(), {m_level}), m_type);
        if (auto inst = m_tctx.mk_class_instance(inst_type)) {
            m_is_linear_ordered_semiring = optional<bool>(true);
            return true;
        } else {
            m_is_linear_ordered_semiring = optional<bool>(false);
            return false;
        }
    }
}

bool arith_instance_manager::is_linear_ordered_comm_ring() {
    if (m_is_linear_ordered_comm_ring) {
        return *m_is_linear_ordered_comm_ring;
    } else {
        expr inst_type = mk_app(mk_constant(get_linear_ordered_comm_ring_name(), {m_level}), m_type);
        if (auto inst = m_tctx.mk_class_instance(inst_type)) {
            m_is_linear_ordered_comm_ring = optional<bool>(true);
            return true;
        } else {
            m_is_linear_ordered_comm_ring = optional<bool>(false);
            return false;
        }
    }
}

bool arith_instance_manager::is_field() {
    if (m_is_field) {
        return *m_is_field;
    } else {
        expr inst_type = mk_app(mk_constant(get_field_name(), {m_level}), m_type);
        if (auto inst = m_tctx.mk_class_instance(inst_type)) {
            m_is_field = optional<bool>(true);
            return true;
        } else {
            m_is_field = optional<bool>(false);
            return false;
        }
    }
}

bool arith_instance_manager::is_discrete_field() {
    if (m_is_discrete_field) {
        return *m_is_discrete_field;
    } else {
        expr inst_type = mk_app(mk_constant(get_discrete_field_name(), {m_level}), m_type);
        if (auto inst = m_tctx.mk_class_instance(inst_type)) {
            m_is_discrete_field = optional<bool>(true);
            return true;
        } else {
            m_is_discrete_field = optional<bool>(false);
            return false;
        }
    }
}

optional<mpz> arith_instance_manager::has_cyclic_numerals() {
    if (!m_has_cyclic_numerals) {
        expr inst_type = mk_app(mk_constant(get_cyclic_numerals_name(), {m_level}), m_type);
        if (auto inst = m_tctx.mk_class_instance(inst_type)) {
            m_has_cyclic_numerals = optional<bool>(true);
            expr bound = m_tctx.whnf(mk_app(mk_constant(get_cyclic_numerals_bound_name(), {m_level}), m_type, *inst));
            if (auto n = to_num(bound)) {
                m_numeral_bound = *n;
                return optional<mpz>(m_numeral_bound);
            } else {
                throw exception(sstream() << "bound in [cyclic_numerals " << m_type << "] must whnf to a numeral\n");
            }
        } else {
            m_has_cyclic_numerals = optional<bool>(false);
            return optional<mpz>();
        }
    } else if (*m_has_cyclic_numerals) {
        return optional<mpz>(m_numeral_bound);
    } else {
        lean_assert(!(*m_has_cyclic_numerals));
        return optional<mpz>();
    }
}

expr arith_instance_manager::get_zero() {
    if (!null(m_zero)) {
        return m_zero;
    } else {
        expr inst_type = mk_app(mk_constant(get_has_zero_name(), {m_level}), m_type);
        if (auto inst = m_tctx.mk_class_instance(inst_type)) {
            m_zero = mk_app(mk_constant(get_zero_name(), {m_level}), m_type, *inst);
            return m_zero;
        } else {
            throw exception(sstream() << "cannot synthesize [has_zero " << m_type << "]\n");
        }
    }
}

expr arith_instance_manager::get_one() {
    if (!null(m_one)) {
        return m_one;
    } else {
        expr inst_type = mk_app(mk_constant(get_has_one_name(), {m_level}), m_type);
        if (auto inst = m_tctx.mk_class_instance(inst_type)) {
            m_one = mk_app(mk_constant(get_one_name(), {m_level}), m_type, *inst);
            return m_one;
        } else {
            throw exception(sstream() << "cannot synthesize [has_one " << m_type << "]\n");
        }
    }
}

expr arith_instance_manager::get_bit0() {
    if (!null(m_bit0)) {
        return m_bit0;
    } else {
        expr inst_type = mk_app(mk_constant(get_has_add_name(), {m_level}), m_type);
        if (auto inst = m_tctx.mk_class_instance(inst_type)) {
            m_bit0 = mk_app(mk_constant(get_bit0_name(), {m_level}), m_type, *inst);
            return m_bit0;
        } else {
            throw exception(sstream() << "cannot synthesize [has_add " << m_type << "]\n");
        }
    }
}

// TODO(dhs): for instances that are used for more than one getter, cache the instances in the structure as well
expr arith_instance_manager::get_bit1() {
    if (!null(m_bit1)) {
        return m_bit1;
    } else {
        expr inst_type1 = mk_app(mk_constant(get_has_one_name(), {m_level}), m_type);
        if (auto inst1 = m_tctx.mk_class_instance(inst_type1)) {
            expr inst_type2 = mk_app(mk_constant(get_has_add_name(), {m_level}), m_type);
            if (auto inst2 = m_tctx.mk_class_instance(inst_type2)) {
                m_bit1 = mk_app(mk_constant(get_bit1_name(), {m_level}), m_type, *inst1, *inst2);
                return m_bit1;
            } else {
                throw exception(sstream() << "cannot synthesize [has_add " << m_type << "]\n");
            }
        } else {
            throw exception(sstream() << "cannot synthesize [has_one " << m_type << "]\n");
        }
    }
}

expr arith_instance_manager::get_add() {
    if (!null(m_add)) {
        return m_add;
    } else {
        expr inst_type = mk_app(mk_constant(get_has_add_name(), {m_level}), m_type);
        if (auto inst = m_tctx.mk_class_instance(inst_type)) {
            m_add = mk_app(mk_constant(get_add_name(), {m_level}), m_type, *inst);
            return m_add;
        } else {
            throw exception(sstream() << "cannot synthesize [has_add " << m_type << "]\n");
        }
    }
}

expr arith_instance_manager::get_mul() {
    if (!null(m_mul)) {
        return m_mul;
    } else {
        expr inst_type = mk_app(mk_constant(get_has_mul_name(), {m_level}), m_type);
        if (auto inst = m_tctx.mk_class_instance(inst_type)) {
            m_mul = mk_app(mk_constant(get_mul_name(), {m_level}), m_type, *inst);
            return m_mul;
        } else {
            throw exception(sstream() << "cannot synthesize [has_mul " << m_type << "]\n");
        }
    }
}

expr arith_instance_manager::get_sub() {
    expr inst_type = mk_app(mk_constant(get_has_sub_name(), {m_level}), m_type);
    if (auto inst = m_tctx.mk_class_instance(inst_type)) {
        return mk_app(mk_constant(get_sub_name(), {m_level}), m_type, *inst);
    } else {
        throw exception(sstream() << "cannot synthesize [has_sub " << m_type << "]\n");
    }
}

expr arith_instance_manager::get_div() {
    expr inst_type = mk_app(mk_constant(get_has_div_name(), {m_level}), m_type);
    if (auto inst = m_tctx.mk_class_instance(inst_type)) {
        return mk_app(mk_constant(get_div_name(), {m_level}), m_type, *inst);
    } else {
        throw exception(sstream() << "cannot synthesize [has_div " << m_type << "]\n");
    }
}

expr arith_instance_manager::get_neg() {
    expr inst_type = mk_app(mk_constant(get_has_neg_name(), {m_level}), m_type);
    if (auto inst = m_tctx.mk_class_instance(inst_type)) {
        return mk_app(mk_constant(get_neg_name(), {m_level}), m_type, *inst);
    } else {
        throw exception(sstream() << "cannot synthesize [has_neg " << m_type << "]\n");
    }
}

expr arith_instance_manager::get_eq() { return mk_app(mk_constant(get_eq_name(), {m_level}), m_type); }

expr arith_instance_manager::get_le() {
    expr inst_type = mk_app(mk_constant(get_has_le_name(), {m_level}), m_type);
    if (auto inst = m_tctx.mk_class_instance(inst_type)) {
        return mk_app(mk_constant(get_le_name(), {m_level}), m_type, *inst);
    } else {
        throw exception(sstream() << "cannot synthesize [has_le " << m_type << "]\n");
    }
}

expr arith_instance_manager::get_ge() {
    expr inst_type = mk_app(mk_constant(get_has_le_name(), {m_level}), m_type);
    if (auto inst = m_tctx.mk_class_instance(inst_type)) {
        return mk_app(mk_constant(get_ge_name(), {m_level}), m_type, *inst);
    } else {
        throw exception(sstream() << "cannot synthesize [has_le " << m_type << "]\n");
    }
}

expr arith_instance_manager::get_lt() {
    expr inst_type = mk_app(mk_constant(get_has_lt_name(), {m_level}), m_type);
    if (auto inst = m_tctx.mk_class_instance(inst_type)) {
        return mk_app(mk_constant(get_lt_name(), {m_level}), m_type, *inst);
    } else {
        throw exception(sstream() << "cannot synthesize [has_lt " << m_type << "]\n");
    }
}

expr arith_instance_manager::get_gt() {
    expr inst_type = mk_app(mk_constant(get_has_lt_name(), {m_level}), m_type);
    if (auto inst = m_tctx.mk_class_instance(inst_type)) {
        return mk_app(mk_constant(get_gt_name(), {m_level}), m_type, *inst);
    } else {
        throw exception(sstream() << "cannot synthesize [has_lt " << m_type << "]\n");
    }
}

// Setup and teardown
void initialize_arith_normalizer_instance_manager() {}
void finalize_arith_normalizer_instance_manager() {}

}
