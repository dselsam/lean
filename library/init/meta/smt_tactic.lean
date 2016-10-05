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

-- Prelim
def bool.to_string_true_false : bool -> string
| tt := "true"
| ff := "false"

def list.to_string_spaces_aux {A : Type*} [has_to_string A] : bool -> list A -> string
| b [] := ""
| tt (x::xs) := to_string x ++ list.to_string_spaces_aux ff xs
| ff (x::xs) := " " ++ to_string x ++ list.to_string_spaces_aux ff xs

def list.to_string_spaces {A : Type*} [has_to_string A] : list A → string :=
list.to_string_spaces_aux tt

-- Basics
@[reducible] definition Numeral : Type := num
@[reducible] definition Symbol : Type := string

instance : has_to_string Numeral := ⟨to_string ∘ nat.of_num⟩

-- SExprs

-- TODO(dhs): hex/binary, strings
@[reducible] definition SpecConstant : Type := Numeral

inductive SExpr : Type
| const : SpecConstant -> SExpr
| symbol : Symbol -> SExpr
| seq : list SExpr -> SExpr

mutual def SExpr.to_string, SExpr.seq_to_string
with SExpr.to_string : SExpr -> string
| (const sc) := to_string sc
| (symbol sym) := sym
| (seq xs) := "(" ++ SExpr.seq_to_string tt xs ++ ")"
with SExpr.seq_to_string : list SExpr -> string
| b [] := ""
| tt (x::xs) := SExpr.to_string x ++ SExpr.seq_to_string xs
| ff (x::xs) := " " ++ SExpr.to_string x ++ SExpr.seq_to_string xs

-- Note: mutual def not yet implemented!
-- instance : has_to_string SExpr := ⟨SExpr.to_string⟩

-- Identifiers
definition Index : Type := Numeral ⊕ Symbol
structure Identifier : Type := (id : Symbol) (args : list Index)

-- Sorts

-- TODO(dhs): allow nested inductive types in structures?
inductive Sort : Type
| mk : Identifier -> list Sort -> Sort

mutual def Sort.to_string, Sort.seq_to_string
with Sort.to_string : Sort -> string
| ⟨id, []⟩ := id
| ⟨id, sorts⟩ := "(" ++ id ++ Sort.seq_to_string ++ ")"
with Sort.seq_to_string : list Sort -> string
| [] := ""
| (s::ss) := " " ++ Sort.to_string s ++ Sort.seq_to_string ss

--instance : has_to_string Sort := ⟨Sort.to_string⟩

-- Attributes
inductive AttributeValue : Type
| const : SpecConstant -> AttributeValue
| sym : Symbol -> AttributeValue
| sexpr : list SExpr -> AttributeValue

structure Attribute : Type := (key : Symbol) (val : option AttributeValue)

-- Terms
definition QualIdentifier : Type := Identifier -- TODO(dhs): (as <id> <sort>)
structure SortedVar : Type := (id : Symbol) (sort : Sort)

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

namespace Examples

def Term.example1 : Term := Term.const 5
def Term.example2 : Term := Term.ident (Identifier.mk "f" []) []
def Term.example3 : Term := Term.tlet [VarBinding.mk "x" Term.example1] Term.example2

end Examples

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






end smt
end tactic
