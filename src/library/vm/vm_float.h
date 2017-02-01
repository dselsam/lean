/*
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include <limits>
#include "library/vm/vm.h"

namespace lean {
vm_obj to_obj(float const & x);
float to_float(vm_obj const & o);

void initialize_vm_float();
void finalize_vm_float();
}
