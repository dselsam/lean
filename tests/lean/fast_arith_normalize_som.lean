import algebra.ring

constants (A : Type.{1}) (A_inst : comm_ring A) (x y z w : A)
attribute [instance] A_inst

set_option arith_normalizer.distribute_mul true
--set_option trace.arith_normalizer.fast true
--set_option pp.all true
#fast_arith_normalize x = x

#fast_arith_normalize x * (y + z) = x * y + x * z
#fast_arith_normalize (x + w) * (y + z) * (w + (x * (z + w)))
