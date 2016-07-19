import algebra.ring

constants (uint32 : Type.{1}) (uint32_cr : comm_ring uint32) (uint32_de : decidable_eq uint32) (uint32_in : inhabited uint32)
          (bw_and bw_or bw_not bw_xor bw_ror32 : uint32 → uint32 → uint32) (bw_not32 : uint32 → uint32)
attribute uint32_cr [instance]
attribute uint32_de [instance]
attribute uint32_in [instance]

constant (map : Π (A B : Type.{1}) [decidable_eq A] [inhabited A], Type.{1})

namespace map
constants (insert : Π {A B : Type.{1}} [decidable_eq A], A → B → map A B → map A B)
constants (lookup : Π {A B : Type.{1}} [decidable_eq A], A → map A B → option B)

end map
