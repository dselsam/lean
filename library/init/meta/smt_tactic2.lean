/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
constants (int real : Type)

namespace expr

@[reducible] meta def mk_Prop : expr := sort level.zero
@[reducible] meta def mk_Type : expr := sort (level.succ level.zero)

end expr

namespace smt
open expr nat

-- Sorts

-- (declare-const x <Sort>)
inductive Sort : Type
| Bool : Sort
| Int : Sort
| Real : Sort
| User : name → list Sort → Sort

namespace Sort
instance : inhabited Sort := ⟨Sort.User `_errorSort []⟩

meta def ofExpr : expr → Sort
| mk_Prop          := Sort.Bool
| (const `int [])  := Sort.Int
| (const `real []) := Sort.Real
| e                := match get_app_fn e with
                      | (const n ls) := Sort.User n (list.map ofExpr $ get_app_args e)
                      | _            := default Sort
                      end

end Sort

-- (declare-sort List 1)
inductive SortDecl : Type
| mk : name → ℕ → SortDecl

namespace SortDecl

instance : inhabited SortDecl := ⟨⟨`_errorSortDecl, 0⟩⟩

meta def ofExprCore (sortName : name) : expr → nat → SortDecl
| (pi _ _ mk_Type b)  k := ofExprCore b (succ k)
| mk_Type             k := ⟨sortName, k⟩
| _                   _ := default SortDecl

meta def ofExpr (n : name) (e : expr) : SortDecl := ofExprCore n e 0

end SortDecl

-- (declare-fun f (Int Real) Bool)
inductive FunDecl : Type
| mk : name → list Sort → Sort → FunDecl

namespace FunDecl

instance : inhabited FunDecl := ⟨⟨`_errorFunDecl, [], default Sort⟩⟩

meta def ofExprCore : expr →  list Sort × Sort
| (pi _ _ dom bod) := match ofExprCore bod with
                      | (xs, x) := ((Sort.ofExpr dom) :: xs, x)
                      end
| bod              := ([], Sort.ofExpr bod)

meta def ofExpr (funName : name) (e : expr) : FunDecl :=
  match ofExprCore e with
  | (xs, x) := ⟨funName, xs, x⟩
  end

end FunDecl

-- Terms

namespace Term

inductive Nullary : Type
| true, false

inductive Unary : Type
| not, implies
| uminus, abs, to_real, to_int, is_int

inductive Binary : Type
| and, or, eq
| plus, sub, times, idiv, mod, div, lt, le, gt, ge

end Term

inductive Term : Type
| nullary : Term.Nullary → Term
| unary   : Term.Unary → Term → Term
| binary  : Term.Binary → Term → Term → Term
| num     : unsigned → Term
| user    : string → list Term → Term
| arrow   : Term → Term → Term

end smt
