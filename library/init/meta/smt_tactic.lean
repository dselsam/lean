/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
prelude
import init.meta.tactic init.meta.attribute init.meta.constructor_tactic
import init.meta.relation_tactics

-- Preliminaries

def bool.to_smt (b : bool) : string := cond b "true" "false"
def num.to_smt (n : num) := to_string (nat.of_num n)

private def list.with_spaces_aux {X : Type} (f : X -> string) : bool -> list X -> string
| b [] := ""
| tt (x::xs) := f x ++ list.with_spaces_aux ff xs
| ff (x::xs) := " " ++ f x ++ list.with_spaces_aux ff xs

def list.with_spaces {X : Type} (f : X -> string) : list X -> string := list.with_spaces_aux f tt

meta constant trustZ3 : expr -> expr

namespace tactic
namespace smt

-- Basics
definition Numeral : Type := num
def Numeral.to_smt := @num.to_smt

definition Symbol : Type := string
def Symbol.to_smt (sym : Symbol) := sym

-- SExprs

-- TODO(dhs): hex/binary, strings
definition SpecConstant : Type := Numeral
def SpecConstant.to_smt := @Numeral.to_smt

inductive SExpr : Type
| const : SpecConstant -> SExpr
| symbol : Symbol -> SExpr
| seq : list SExpr -> SExpr

meta def SExpr.to_smt : SExpr -> string
| (SExpr.const sc) := sc~>to_smt
| (SExpr.symbol sym) := sym
| (SExpr.seq xs) := "(" ++ list.with_spaces SExpr.to_smt xs ++ ")"

-- Identifiers
definition Index : Type := Numeral ⊕ Symbol
definition Index.to_smt : Index -> string
| (sum.inl n) := n~>to_smt
| (sum.inr s) := s~>to_smt

structure Identifier : Type := (id : Symbol) (args : list Index)
meta def Identifier.to_smt : Identifier -> string
| ⟨id, []⟩ := id~>to_smt
| ⟨id, idxs⟩ := "(_ " ++ id~>to_smt ++ " " ++ list.with_spaces Index.to_smt idxs ++ ")"

-- Sorts

inductive Sort : Type | mk : Identifier -> list Sort -> Sort
meta def Sort.to_smt : Sort -> string
| (Sort.mk id []) := id~>to_smt
| (Sort.mk id sorts) := "(" ++ id~>to_smt ++ " " ++ list.with_spaces Sort.to_smt sorts ++ ")"

-- Attributes
inductive AttributeValue : Type
| const : SpecConstant -> AttributeValue
| sym : Symbol -> AttributeValue
| sexpr : list SExpr -> AttributeValue

structure Attribute : Type := (key : Symbol) (val : option AttributeValue)
meta def Attribute.to_smt : Attribute -> string
| attr := "" -- TODO(dhs): generate strings from attributes

-- Terms
definition QualIdentifier : Type := Identifier -- TODO(dhs): (as <id> <sort>)
structure SortedVar : Type := (id : Symbol) (sort : Sort)

meta def SortedVar.to_smt : SortedVar -> string
| ⟨id, sort⟩ := "(" ++ id~>to_smt ++ " " ++ sort~>to_smt ++ ")"

-- Note: was using mutual inductive here for VarBinding as in the standard,
-- but mutual def is not implemented yet.
inductive Term : Type
| const : SpecConstant -> Term
| ident : QualIdentifier -> list Term -> Term
| tlet : list (prod Symbol Term) -> Term -> Term
| tforall : list SortedVar -> Term -> Term
| texists : list SortedVar -> Term -> Term
| tattr : list Attribute -> Term -> Term

meta def VarBinding.to_smt (f : Term -> string) : prod Symbol Term -> string
| ⟨id, t⟩ := "(" ++ id~>to_smt ++ " " ++ f t ++ ")"

meta def Term.to_smt : Term -> string
| (Term.const sc) := sc~>to_smt
| (Term.ident qid []) := qid~>to_smt
| (Term.ident qid args) := "(" ++ qid~>to_smt ++ " " ++ list.with_spaces Term.to_smt args ++ ")"
--| (Term.tlet vbs t) := "(let (" ++ list.with_spaces (VarBinding.to_smt Term.to_smt) vbs ++ ") " ++ Term.to_smt t ++ ")"
| (Term.tlet vbs t) := "<assert-failure, erase_irrelevant:160>"
| (Term.tforall svs t) := "(forall (" ++ list.with_spaces SortedVar.to_smt svs ++ ") " ++ Term.to_smt t ++ ")"
| (Term.texists svs t) := "(exists (" ++ list.with_spaces SortedVar.to_smt svs ++ ") " ++ Term.to_smt t ++ ")"
| (Term.tattr attrs t) := "(! " ++ Term.to_smt t ++ " " ++ list.with_spaces Attribute.to_smt attrs ++ ")"


namespace Examples

def Term.example1 : Term := Term.const (5 : num)
def Term.example2 : Term := Term.ident (Identifier.mk "f" []) []
def Term.example3 : Term := Term.tforall [SortedVar.mk "x" (Sort.mk (Identifier.mk "X" []) [])] Term.example2

vm_eval Term.example3~>to_smt
end Examples


-- Command Options
inductive CommandOption : Type
| produceModels : bool -> CommandOption
| produceUnsatCores : bool -> CommandOption

-- TODO(dhs): many other options
def CommandOption.to_smt : CommandOption -> string
| (CommandOption.produceModels b) := ":produce-models " ++ b~>to_smt
| (CommandOption.produceUnsatCores b) := ":produce-unsat-cores " ++ b~>to_smt

-- Commands

structure FunDef : Type := (id : Symbol) (vars : list SortedVar) (sort : Sort) (val : Term)

meta def FunDef.to_smt : FunDef -> string
| ⟨id, vars, sort, val⟩ := id ++ " (" ++ list.with_spaces SortedVar.to_smt vars ++ ") " ++ sort~>to_smt ++ " " ++ val~>to_smt

inductive Command : Type
| assert : Term -> Command
| checkSat : Command
| declareConst : Symbol -> Sort -> Command
| declareFun : Symbol -> list Sort -> Sort -> Command
| declareSort : Symbol -> Numeral -> Command
| getModel : Command
| getUnsatAssumptions : Command
| getUnsatCore : Command
| setOption : CommandOption -> Command
-- TODO(dhs): many others

meta def Command.to_smt : Command -> string
| (Command.assert t) := "(assert " ++ t~>to_smt ++ ")"
| (Command.checkSat) := "(check-sat)"
| (Command.declareConst id sort) := "(declare-const " ++ id~>to_smt ++ " " ++ sort~>to_smt ++ ")"
| (Command.declareFun id sorts sort) := "(declare-const " ++ id~>to_smt ++ " (" ++ list.with_spaces Sort.to_smt sorts ++ ") " ++ sort~>to_smt ++ ")"
| (Command.declareSort id n) := "(declare-sort " ++ id~>to_smt ++ " " ++ n~>to_smt ++ ")"
| (Command.getModel) := "(get-model)"
| (Command.getUnsatAssumptions) := "(get-unsat-assumptions)"
| (Command.getUnsatCore) := "(get-unsat-core)"
| (Command.setOption co) := "(set-option " ++ co~>to_smt ++ ")"

-- Command Responses
inductive ErrorBehavior : Type | immediateExit, continuedExecution
inductive ModelResponse : Type | fundef : FunDef -> ModelResponse
inductive CheckSatResponse : Type | sat,  unsat, unknown

inductive CommandResponse : Type
| checkSat : CheckSatResponse -> CommandResponse
| getModel : list ModelResponse -> CommandResponse
| getUnsatAssumptions : list Symbol -> CommandResponse
| getUnsatCore : list Symbol -> CommandResponse

meta constant callZ3 : string -> tactic string

namespace Examples

example : false :=
by do x ←  callZ3 Command.checkSat~>to_smt,
      trace x

end Examples



end smt
end tactic
