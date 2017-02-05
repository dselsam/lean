/*
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include <Eigen/Dense>
#include <limits>
#include "library/vm/vm.h"

namespace lean {
vm_obj to_obj(Eigen::ArrayXXf const & v);
Eigen::ArrayXXf const & to_eigen(vm_obj const & o);

void initialize_vm_eigen();
void finalize_vm_eigen();
}
