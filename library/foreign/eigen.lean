import foreign.float

namespace eigen

def tshape : Type := list ℕ

def tsize : tshape → ℕ
| [] := 1
| (d::ds) := d * tsize ds

meta constant T : tshape → Type

meta constant to_string {shape : tshape} : T shape → string

meta instance {shape : tshape} : has_to_string (T shape) :=
has_to_string.mk to_string

meta constant box (α : float) : T []

meta def π : T [] := box float.pi

--meta constant const (α : T []) : Π (shape : tshape), T shape
--meta constant lift₁ (f : T [] → T []) : Π {shape : tshape}, T shape → T shape
--meta constant lift₂ (f : T [] → T [] → T []) : Π {shape : tshape}, T shape → T shape → T shape

meta constants zero one : Π (shape : tshape), T shape

meta constants neg inv log exp sqrt tanh : Π {shape : tshape}, T shape → T shape
meta constants add mul sub div : Π {shape : tshape}, T shape → T shape → T shape

meta constant smul (α : T []) : Π {shape : tshape}, T shape → T shape

meta constants sum prod : Π {shape : tshape}, T shape → T []

meta constant get_row {m n : ℕ} (M : T [m, n]) (ridx : fin m) : T [n]
meta constant get_col {m n : ℕ} (M : T [m, n]) (cidx : fin n) : T [m]

meta constant get_col_range {m n : ℕ} (M : T [m, n]) (cidx : fin n) (ncols_to_take : ℕ) : T [m, ncols_to_take]

meta constant gemv {m n : ℕ} (M : T [m, n]) (x : T [n]) : T [m]
meta constant gemm {m n p : ℕ} (M : T [m, n]) (N : T [n, p]) : T [m, p]

end eigen

namespace Test
open eigen

meta def t₀ : T [] := eigen.add (eigen.one _) (eigen.one _)
meta def t₁ : T [2] := eigen.add (eigen.one _) (eigen.one _)
meta def t₂ : T [2, 2] := eigen.add (eigen.one _) (eigen.one _)
meta def t₃ : T [2, 2, 2] := eigen.add (eigen.one _) (eigen.one _)

vm_eval t₀
vm_eval t₁
vm_eval t₂
vm_eval t₃

--vm_eval gemm t₁ t₁

end Test
