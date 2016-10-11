/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
prelude
import init.meta.tactic init.meta.attribute init.meta.constructor_tactic
import init.meta.relation_tactics init.meta.rb_map
import init.instances
import init.monad init.monad_combinators init.monad_trans init.state

set_option eqn_compiler.max_steps 1000

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
structure SortDecl : Type := (id : Symbol) (numArgs : Numeral)

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

def Term.false : Term := Term.ident (Identifier.mk "false" []) []
def Term.true : Term := Term.ident (Identifier.mk "true" []) []

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
structure FunDecl : Type := (id : Symbol) (vars : list Sort) (sort : Sort)
structure FunDef : Type := (id : Symbol) (vars : list SortedVar) (sort : Sort) (val : Term)

meta def FunDef.to_smt : FunDef -> string
| ⟨id, vars, sort, val⟩ := id ++ " (" ++ list.with_spaces SortedVar.to_smt vars ++ ") " ++ sort~>to_smt ++ " " ++ val~>to_smt

inductive Command : Type
| assert : Term -> Command
| checkSat : Command
| declareFun : FunDecl -> Command
| declareSort : SortDecl -> Command
| getModel : Command
| getUnsatAssumptions : Command
| getUnsatCore : Command
| setOption : CommandOption -> Command

meta def Command.to_smt : Command -> string
| (Command.assert t) := "(assert " ++ t~>to_smt ++ ")"
| (Command.checkSat) := "(check-sat)"
| (Command.declareSort ⟨id, n⟩) := "(declare-sort " ++ id~>to_smt ++ " " ++ n~>to_smt ++ ")"
| (Command.declareFun ⟨id, sorts, sort⟩) := "(declare-const " ++ id~>to_smt ++ " (" ++ list.with_spaces Sort.to_smt sorts ++ ") " ++ sort~>to_smt ++ ")"
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

meta def Z3CanProve (cmds : list Command) : tactic bool :=
do ret ← callZ3 (list.with_spaces Command.to_smt cmds),
   return $ if ret = "unsat\n" then tt else ff

namespace Examples
print "Checking Z3 connection..."

example : true :=
by do should_be_true ← Z3CanProve [Command.assert Term.false, Command.checkSat],
      trace "should be true:",
      trace should_be_true,
      should_be_false ← Z3CanProve [Command.assert Term.true, Command.checkSat],
      trace "should be false:",
      trace should_be_false,
      triv

end Examples

meta structure BuildSMTProblemState : Type := (sorts : rb_map name SortDecl) (fdecls : rb_map name FunDecl) (assertions : list Term)
@[reducible] meta def SMTMethod : Type -> Type := stateT BuildSMTProblemState tactic

meta def liftSMT {A : Type} (tac : tactic A) : SMTMethod A := λ s, do res ← tac, return (res, s)

namespace SMTMethod
open monad

meta def initBuildSMTProblemState : BuildSMTProblemState := ⟨rb_map.mk name SortDecl, rb_map.mk name FunDecl, []⟩

-- Add
meta def addSort (n : name) (sort : SortDecl) : SMTMethod unit :=
do s ← stateT.read,
   match s with
   | ⟨sorts, funDecls, assertions⟩ := stateT.write $ ⟨rb_map.insert sorts n sort, funDecls, assertions⟩
   end

meta def addFunDef (n : name) (funDecl : FunDecl) : SMTMethod unit :=
do s ← stateT.read,
   match s with
   | ⟨sorts, funDecls, assertions⟩ := stateT.write $ ⟨sorts, rb_map.insert funDecls n funDecl, assertions⟩
   end

meta def addAssertion (term : Term) : SMTMethod unit :=
do s ← stateT.read,
   match s with
   | ⟨sorts, funDecls, assertions⟩ := stateT.write $ ⟨sorts, funDecls, assertions ++ [term]⟩
   end

-- Find
meta def findSort (n : name) : SMTMethod (option SortDecl) :=
do s ← stateT.read,
   match s with
   | ⟨sorts, funDecls, assertions⟩ := return $ rb_map.find sorts n
   end

meta def findFunDef (n : name) : SMTMethod (option FunDecl) :=
do s ← stateT.read,
   match s with
   | ⟨sorts, funDecls, assertions⟩ := return $ rb_map.find funDecls n
   end

-- Contains
meta def containsSort (n : name) : SMTMethod bool :=
do s ← stateT.read,
   match s with
   | ⟨sorts, funDecls, assertions⟩ := return $ rb_map.contains sorts n
   end

meta def containsFunDef (n : name) : SMTMethod bool :=
do s ← stateT.read,
   match s with
   | ⟨sorts, funDecls, assertions⟩ := return $ rb_map.contains funDecls n
   end

-- The main expression traversal function
meta def traverseExpr : expr -> SMTMethod Term
| (expr.app (expr.const `not []) e) := do t ← traverseExpr e, return $ Term.ident ⟨"not", []⟩ [t]
| (expr.const `true []) := return $ Term.ident ⟨"true", []⟩ []
| (expr.const `false []) := return $ Term.ident ⟨"false", []⟩ []
| _ := return $ Term.ident ⟨"FAIL", []⟩ []
-- TODO(dhs): much more stuff to handle

-- TODO(dhs): need to create the sortDecls and the funDecls
meta def processType : name -> expr -> SMTMethod unit :=
λ (n : name) (e : expr),
do t     ← traverseExpr e,
   eType ← liftSMT (infer_type e),
   if eType = expr.prop then addAssertion t else
   if expr.is_sort eType then addSort n t else
   addFunDecl n t

--vm_eval (processHypothesis (expr.const `true []) initBuildSMTProblemState).1~>to_smt

meta def buildSMTProblemCore (hyps : list expr) (goal : expr) : SMTMethod unit :=
do hypNames ← return $ list.map expr.local_uniq_name hyps,
   hypTypes ← liftSMT $ mapM infer_type hyps,
   mapM processType hypTypes,
   processHypothesis (expr.app (expr.const `not []) goal),
   return ()

meta def buildSMTProblem : tactic (list Command) :=
do hyps  ← local_context,
   trace "\nlocal_context: ",
   trace hyps,
   tgt   ← target,
   state ← stateT.exec (buildSMTProblemCore hyps tgt) initBuildSMTProblemState,
   match state with
   | ⟨sorts, funDecls, assertions⟩ := return $
     list.map Command.declareSort (rb_map.values sorts)
     ++ list.map Command.declareFun (rb_map.values funDecls)
     ++ list.map Command.assert assertions
   end

example (h₁ h₂ : true) : true :=
by do cmds : list Command ← buildSMTProblem,
      strs : list string ← return $ list.map Command.to_smt cmds,
      trace "\nSMT Problem: ",
      trace strs,
      failed

exit
end BuildSMTProblem



-- meta constant {u₁ u₂} rb_map : Type u₁ → Type u₂ → Type (max u₁ u₂ 1)




/-
TODO(dhs): the next thing to do is to take a goal and construct a list of Commands.
We will not implement anything fancy yet, just the "Core" theory and arithmetic
for now.

The basic idea is as follows:

We maintain:
1. A map from sort names to arities (X |-> 0, Y |-> 1)
2. A map from names to function defs (x |-> {[], X []}, y |-> {[X], Y X})
3. A list of asserted terms

We may decide to use StateT tactic for this, although it seems heavy-handed.

We traverse each hypothesis in sequence. At every subexpression, we give each theory a chance to "claim" the expression.

Example: `(@add nat _ _ _)` will be claimed by arithmetic. Note that implicit arguments may be taken into account.

If no one (excluding UF) claims it, we may throw an error if it is:
1. A pi that is not in Prop
2. A lambda
3. A macro

Otherwise, we add the operator to our set of function defs (if necessary).

Either way, we recursively visit the subterms. If the type of the hypothesis is a Prop, then we build up a Term object as we go along, and Assert the term at the end.

The theory processors will be responsible for returning the subexpressions that need to be processed.
For the UF case, all arguments will be considered important subterms.

We traverse the goal just like any other hypothesis, except we negate it at the end.

There are many issues with the approach I have just described.
1. Dependent types outside of Prop
   - Can I handle [M : matrix m n]? What about [M : matrix (m1 + m2) (n1 + n2)]? I don't really care.
   - But what about bitvectors? For sure I need these. Maybe they can be special-cased? The bit-vector theory can claim them.
   - I think I can be very conservative for now about what kind of dependent types I can support.

-/



end smt
end tactic
