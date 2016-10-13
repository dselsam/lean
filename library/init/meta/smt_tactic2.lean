/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
constants (int real : Type)

set_option eqn_compiler.max_steps 1000

namespace Util

private def list.withSpacesCore {X : Type} (f : X -> string) : bool -> list X -> string
| b [] := ""
| tt (x::xs) := f x ++ list.withSpacesCore ff xs
| ff (x::xs) := " " ++ f x ++ list.withSpacesCore ff xs

def list.withSpaces {X : Type} (f : X -> string) : list X -> string := list.withSpacesCore f tt

end Util

open Util

namespace expr

@[reducible] meta def mk_Prop : expr := sort level.zero
@[reducible] meta def mk_Type : expr := sort (level.succ level.zero)
@[reducible] meta def mk_Type₂ : expr := sort (level.succ $ level.succ level.zero)

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
| (User n xs) := "(" ++ n~>to_string ++ " " ++ list.withSpaces toSMT xs ++ ")"

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

meta def toSMT : SortDecl → string
| (mk n k) := n~>to_string ++ " " ++ k~>to_string

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

meta def toSMT : FunDecl → string
| (mk n xs x) := n~>to_string ++ " (" ++ list.withSpaces Sort.toSMT xs ++ ") " ++ Sort.toSMT x

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
| uminus, abs --, to_real, to_int, is_int

meta def Unary.toSMT : Unary → string
| not     := "not"
| implies := "=>"
| uminus  := "-"
| abs     := "abs"

inductive Binary : Type
| and, or, eq
| plus, sub, times, idiv, mod, div, lt, le, gt, ge

meta def Binary.toSMT : Binary → string
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
| (user c ts)      := "(" ++ c~>to_string ++ " " ++ list.withSpaces toSMT ts ++ ")"

meta def ofExpr : expr → Term
| (const `true [])                  := nullary Nullary.true
| (const `false [])                 := nullary Nullary.false

| (app (const `not []) e)           := unary Unary.not (ofExpr e)
| (app (const `implies []) e)       := unary Unary.implies (ofExpr e)

| (app (const `neg []) e)           := unary Unary.uminus (ofExpr e)
| (app (const `abs []) e)           := unary Unary.abs (ofExpr e)

| (app (const `and [])   (app e₁ e₂)) := binary Binary.and (ofExpr e₁) (ofExpr e₂)
| (app (const `or [])    (app e₁ e₂)) := binary Binary.or  (ofExpr e₁) (ofExpr e₂)
| (app (const `eq [])    (app e₁ e₂)) := binary Binary.eq  (ofExpr e₁) (ofExpr e₂)

| (app (const `plus [])  (app e₁ e₂)) := binary Binary.plus (ofExpr e₁) (ofExpr e₂)
| (app (const `sub [])   (app e₁ e₂)) := binary Binary.sub (ofExpr e₁) (ofExpr e₂)
| (app (const `times []) (app e₁ e₂)) := binary Binary.times (ofExpr e₁) (ofExpr e₂)
| (app (const `idiv [])  (app e₁ e₂)) := binary Binary.idiv (ofExpr e₁) (ofExpr e₂)
| (app (const `mod [])   (app e₁ e₂)) := binary Binary.mod (ofExpr e₁) (ofExpr e₂)
| (app (const `div [])   (app e₁ e₂)) := binary Binary.div (ofExpr e₁) (ofExpr e₂)
| (app (const `lt [])    (app e₁ e₂)) := binary Binary.lt (ofExpr e₁) (ofExpr e₂)
| (app (const `le [])    (app e₁ e₂)) := binary Binary.le (ofExpr e₁) (ofExpr e₂)
| (app (const `gt [])    (app e₁ e₂)) := binary Binary.gt (ofExpr e₁) (ofExpr e₂)
| (app (const `ge [])    (app e₁ e₂)) := binary Binary.ge (ofExpr e₁) (ofExpr e₂)

| e := match (get_app_fn e, get_app_args e) with
       | (const userName [], args) := user userName (list.map ofExpr args)
       | _                         := default Term
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
do hypName ← return $ local_uniq_name hyp,
   hypType ← infer_type hyp,
   hypTypeType ← infer_type hypType,
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

example (X : Type) (Y : Type → Type) (x : X) (f g : X → Y int) (H : f x = g x) : false :=
by do commands ← goalToCommands,
      trace $ list.withSpaces Command.toSMT commands,
      failed








end smt
