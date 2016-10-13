/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
constants (Int Real : Type)
set_option pp.all true
set_option eqn_compiler.max_steps 1000

namespace Util

private def list.withSepCore {X : Type} (f : X -> string) (sep : string) : bool -> list X -> string
| b [] := ""
| tt (x::xs) := f x ++ list.withSepCore ff xs
| ff (x::xs) := sep ++ f x ++ list.withSepCore ff xs

def list.withSep {X : Type} (f : X -> string) (sep : string) : list X -> string := list.withSepCore f sep tt

end Util

open Util

namespace level

@[reducible, pattern] definition one : level := succ zero
@[reducible, pattern] definition two : level := succ one

end level

namespace expr

@[reducible, pattern] meta def mk_Prop : expr := sort level.zero
@[reducible, pattern] meta def mk_Type : expr := sort level.one
@[reducible, pattern] meta def mk_Type₂ : expr := sort level.two

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

meta def toSMT : Sort → string
| Bool        := "Bool"
| Int         := "Int"
| Real        := "Real"
| (User n []) := n~>to_string
| (User n xs) := "(" ++ n~>to_string ++ " " ++ list.withSep toSMT " " xs ++ ")"

meta def ofExpr : expr → Sort
| mk_Prop          := Bool
| (const `Int [])  := Int
| (const `Real []) := Real
| e                := match get_app_fn e with
                      | (local_const _ n _ _) := User n (list.map ofExpr $ get_app_args e)
                      | f                     := User (mk_str_name f~>to_string "SORT_ERROR") []
                      end

end Sort

-- (declare-sort List 1)
inductive SortDecl : Type
| mk : name → ℕ → SortDecl

namespace SortDecl

instance : inhabited SortDecl := ⟨⟨`_errorSortDecl, 0⟩⟩

meta def toSMT : SortDecl → string
| (mk n k) := n~>to_string ++ " " ++ k~>to_string

meta def ofExprCore (sortName : name) : expr → nat → SortDecl
| (pi _ _ mk_Type b)  k := ofExprCore b (succ k)
| mk_Type             k := ⟨sortName, k⟩
| e                   _ := ⟨mk_str_name e~>to_string "SORTDECL_ERROR", 0⟩

meta def ofExpr (n : name) (e : expr) : SortDecl := ofExprCore n e 0

end SortDecl

-- (declare-fun f (Int Real) Bool)
inductive FunDecl : Type
| mk : name → list Sort → Sort → FunDecl

namespace FunDecl

instance : inhabited FunDecl := ⟨⟨`_errorFunDecl, [], default Sort⟩⟩

meta def toSMT : FunDecl → string
| (mk n xs x) := n~>to_string ++ " (" ++ list.withSep Sort.toSMT " " xs ++ ") " ++ Sort.toSMT x

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

meta def Nullary.toSMT : Nullary → string
| true := "true"
| false := "false"

inductive Unary : Type
| not, implies
| uminus, abs --, to_Real, to_Int, is_Int

namespace Unary
meta def toSMT : Unary → string
| not     := "not"
| implies := "=>"
| uminus  := "-"
| abs     := "abs"
end Unary

inductive Binary : Type
| and, or, eq
| plus, sub, times, idiv, mod, div, lt, le, gt, ge

namespace Binary
meta def toSMT : Binary → string
| and     := "and"
| or      := "or"
| eq      := "="
| plus    := "+"
| sub     := "-"
| times   := "*"
| idiv    := "div"
| mod     := "mod"
| div     := "/"
| lt      := "<"
| le      := "<="
| gt      := ">"
| ge      := ">="
end Binary

end Term

inductive Term : Type
| nullary : Term.Nullary → Term
| unary   : Term.Unary → Term → Term
| binary  : Term.Binary → Term → Term → Term
| num     : nat → Term
| user    : name → list Term → Term

namespace Term

instance : inhabited Term := ⟨user `_errorTerm []⟩

meta def toSMT : Term → string
| (nullary c)      := c~>toSMT
| (unary c t)      := "(" ++ c~>toSMT ++ " " ++ toSMT t ++ ")"
| (binary c t₁ t₂) := "(" ++ c~>toSMT ++ " " ++ toSMT t₁ ++ " " ++ toSMT t₂ ++ ")"
| (num k)          := k~>to_string
| (user c [])      := c~>to_string
| (user c ts)      := "(" ++ c~>to_string ++ " " ++ list.withSep toSMT " " ts ++ ")"

meta def ofExpr : expr → Term
| (const `true [])                  := nullary Nullary.true
| (const `false [])                 := nullary Nullary.false

| (app (const `not []) e)           := unary Unary.not (ofExpr e)
| (app (const `implies []) e)       := unary Unary.implies (ofExpr e)

| (app (const `neg []) e)           := unary Unary.uminus (ofExpr e)
| (app (const `abs []) e)           := unary Unary.abs (ofExpr e)

| (app (app (app (const `eq ls) _) e₁) e₂) := binary Binary.eq (ofExpr e₁) (ofExpr e₂)

| (app (app (const `and []) e₁) e₂) := binary Binary.and (ofExpr e₁) (ofExpr e₂)
| (app (app (const `or []) e₁) e₂)  := binary Binary.or (ofExpr e₁) (ofExpr e₂)

-- TODO(dhs): none of this arith stuff will work as is, because of type classes
-- Do we want to strip them during pre-processing or strip them here?

| e := match (get_app_fn e, get_app_args e) with
       | (local_const _ userName _ _, args) := user userName (list.map ofExpr args)
       | _                                := user (mk_str_name e~>to_string "TERM_ERROR") [] -- ERROR
       end

end Term

inductive Command : Type
| declareSort : SortDecl → Command
| declareFun  : FunDecl → Command
| assert      : Term → Command

namespace Command

meta def toSMT : Command -> string
| (declareSort sortDecl) := "(declare-sort " ++ sortDecl~>toSMT ++ ")"
| (declareFun funDecl) := "(declare-fun " ++ funDecl~>toSMT ++ ")"
| (assert t) := "(assert " ++ t~>toSMT ++ ")"

open tactic

meta def ofHypothesis (hyp : expr) : tactic Command :=
do hypName ← return $ local_pp_name hyp,
   hypType ← infer_type hyp,
   hypTypeType ← infer_type hypType,
--   trace (hypName, hypType, hypTypeType),
   match hypTypeType with
   | mk_Prop  := return $ assert (Term.ofExpr hypType)
   | mk_Type  := return $ declareFun (FunDecl.ofExpr hypName hypType)
   | mk_Type₂ := return $ declareSort (SortDecl.ofExpr hypName hypType)
   | _        := fail $ "unexpected Type of hypothesis: " ++ expr.to_string hypType
   end

end Command

open tactic monad

meta def goalToCommands : tactic (list Command) :=
do hyps  ← local_context,
   tgt   ← target,
   if not (tgt = expr.const `false [])
   then fail "expecting goal to be false"
   else mapM Command.ofHypothesis hyps

example (X : Type) (Y : Type → Type) (x : X) (f g : X → Y Int) (H : f x = g x) : false :=
by do commands ← goalToCommands,
      trace $ list.withSep Command.toSMT "\n" commands,
      failed








end smt
