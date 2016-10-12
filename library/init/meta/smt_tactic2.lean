/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
constants (int real : Type)

namespace expr

@[reducible] definition prop : expr := sort zero
@[reducible] definition type : expr := sort (succ zero)

end expr

namespace smt
open expr level

-- Sorts

inductive Sort : Type
| Bool : Sort
| Int : Sort
| Real : Sort
| User : name → list Sort → Sort

instance : inhabited Sort := ⟨Sort.Bool⟩

meta def exprToSort : expr → Sort
| prop      := Sort.Bool
| (const `int [])  := Sort.Int
| (const `real []) := Sort.Real
| e                := match get_app_fn e with
                      | (const n ls) := Sort.User n (list.map exprToSort $ get_app_args e)
                      | _            := default Sort
                      end

-- Declarations

inductive SortDecl : Type
| mk : name → ℕ → SortDecl

instance : inhabited SortDecl := ⟨SortDecl.mk SortDecl 0⟩



meta def exprToSortDeclCore (sortName : name) : expr → nat → SortDecl
| (pi n bi type e) k := exprToSortDecl (succ k) e
| type             k := SortDecl sortName k

meta def exprToSortDecl (n : name) (e : expr) : SortDecl := exprToSortDeclCore n e 0






inductive FunDecl : Type
| mk : string → list Sort → Sort → FunDecl

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

--


end smt
-/
