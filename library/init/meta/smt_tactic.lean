/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
prelude
import init.meta.tactic init.meta.attribute init.meta.constructor_tactic
import init.meta.relation_tactics

namespace tactic
namespace smt

-- Preliminaries

private def list.with_spaces_aux {X : Type} (f : X -> string) : bool -> list X -> string
| b [] := ""
| tt (x::xs) := f x ++ list.with_spaces_aux ff xs
| ff (x::xs) := " " ++ f x ++ list.with_spaces_aux ff xs

def list.with_spaces {X : Type} (f : X -> string) : list X -> string := list.with_spaces_aux f tt

def bool.to_smt (b : bool) : string := cond b "true" "false"
def num.to_smt (n : num) := to_string (nat.of_num n)

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

-- Terms
definition QualIdentifier : Type := Identifier -- TODO(dhs): (as <id> <sort>)
structure SortedVar : Type := (id : Symbol) (sort : Sort)

meta def SortedVar.to_smt : SortedVar -> string
| ⟨id, sort⟩ := "(" ++ id~>to_smt ++ " " ++ sort~>to_smt ++ ")"

mutual inductive Term, VarBinding
with Term : Type
| const : SpecConstant -> Term
| ident : QualIdentifier -> list Term -> Term
| tlet : list VarBinding -> Term -> Term
| tforall : list SortedVar -> Term -> Term
| texists : list SortedVar -> Term -> Term
| tattr : list Attribute -> Term -> Term
with VarBinding : Type
| mk : Symbol -> Term -> VarBinding

-- Deadend -- need mutual definition to define the `to_smt` function
/-
mutual def Term.to_string, VarBinding.to_string
with Term.to_string : Term -> string
| (Term.const sc) := to_string sc
| (Term.ident qid []) := to_string qid
| (Term.ident qid ts) := "(_ " ++ to_string qid ++ list.to_string_spaces ts ++ ")"
| (Term.tlet vbs t) := "(let (" ++ list.to_string_spaces vbs ++ ") " ++ Term.to_string t ++ ")"
| (Term.tforall svs t) := "(forall (" ++ list.to_string_spaces svs ++ ") " ++ Term.to_string t ++ ")"
| (Term.texists svs t) := "(exists (" ++ list.to_string_spaces svs ++ ") " ++ Term.to_string t ++ ")"
| (Term.tattr attrs t) := "(! " ++ Term.to_string t ++ list.to_string_spaces attrs ++ ")"
with VarBinding.to_string : VarBinding -> string
| (VarBinding.mk id t) := "(" ++ id ++ " " ++ Term.to_string t ++ ")"

namespace Examples

def Term.example1 : Term := Term.const (5 : num)
def Term.example2 : Term := Term.ident (Identifier.mk "f" []) []
def Term.example3 : Term := Term.tlet [VarBinding.mk "x" Term.example1] Term.example2

end Examples


-- Command Options

inductive CommandOption : Type
| produceModels : bool -> CommandOption
| produceUnsatCores : bool -> CommandOption
-- TODO(dhs): many other options

def CommandOption.to_string : CommandOption -> string
| (CommandOption.produceModels b) := "(set-option :produce-models " ++ bool.to_string_true_false b ++ ")"
| (CommandOption.produceUnsatCores b) := "(set-option :produce-unsat-cores " ++ bool.to_string_true_false b ++ ")"

-- Commands
structure FunDec : Type := (id : Symbol) (vars : list SortedVar) (sort : Sort)
structure FunDef : Type := (id : Symbol) (vars : list SortedVar) (sort : Sort) (val : Term)

def FunDec.to_string : FunDec -> string
| ⟨id, vars, sort⟩ := "(" ++ id ++ " (" ++ list.to_string_spaces vars ++ ") " ++ to_string sort ++ ")"

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

--def Command.to_string : Command -> string
--| (assert t) := "(assert " ++ to_string


-- Command Responses
inductive ErrorBehavior : Type | immediateExit, continuedExecution
inductive ModelResponse : Type | fundef : FunDef -> ModelResponse
inductive CheckSatResponse : Type | sat,  unsat, unknown
definition GetModelResponse : Type := list ModelResponse
definition GetUnsatAssumptionsResponse : Type := list Symbol
definition GetUnsatCoreResponse : Type := list Symbol

inductive CommandResponse : Type
| checkSat : CheckSatResponse -> CommandResponse
| getModel : GetModelResponse -> CommandResponse
| getUnsatAssumptions : GetUnsatAssumptionsResponse -> CommandResponse
| getUnsatCore : GetUnsatCoreResponse -> CommandResponse





-/

end smt
end tactic
