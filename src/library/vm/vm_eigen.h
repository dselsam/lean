/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <Eigen/Dense>
#include <limits>
#include "library/vm/vm.h"

namespace lean {
vm_obj to_obj(Eigen::ArrayXf const & v);
Eigen::ArrayXf to_eigen(vm_obj const & o);

void initialize_vm_eigen();
void finalize_vm_eigen();
}
