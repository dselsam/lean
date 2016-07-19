import algebra.ring

constants (uint32 : Type.{1}) (uint32_cr : comm_ring uint32) (uint32_de : decidable_eq uint32) (uint32_le : has_le uint32)
          (bw_and bw_or bw_not bw_xor bw_ror32 : uint32 → uint32 → uint32) (bw_not32 : uint32 → uint32)
attribute uint32_cr [instance]
attribute uint32_de [instance]
attribute uint32_le [instance]

constant (Map : Π (A B : Type) [decidable_eq A], Type)

namespace Map
constants (empty :  Π {A B : Type} [decidable_eq A], Map A B)
constants (insert : Π {A B : Type} [decidable_eq A], A → B → Map A B → Map A B)
constants (lookup : Π {A B : Type} [decidable_eq A], A → Map A B → option B)

end Map

definition to_bool (P : Prop) [decidable P] : bool := if P then tt else ff
