/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import smt.theory smt.util

set_option pp.all true
set_option eqn_compiler.max_steps 10000

namespace tactic
namespace smt

/-
Meta constants
--------------
These are the only two meta-constants in the SMT library.

The first (trustZ3) simply wraps an expression in the Z3 macro and
claims to provide a proof for it.

The second (callZ3) simply executes Z3 on the command line on the
string passed, and returns the result as a string.

We keep this extra flexibility so that we can recover more information
from Z3 in the future, e.g. models.
-/
private meta constant trustZ3 : expr -> tactic expr
private meta constant callZ3 : string -> tactic string

open expr nat monad

-- Sorts

-- (declare-const x <Sort>)
inductive Sort : Type
| Bool : Sort
| Int : Sort
| Real : Sort
| BitVec : ℕ → Sort
| User : name → list Sort → Sort

namespace Sort

instance : inhabited Sort := ⟨Sort.User `_errorSort []⟩

meta def toSMT : Sort → string
| Bool        := "Bool"
| Int         := "Int"
| Real        := "Real"
| (BitVec n)  := "(_ BitVec " ++ n~>to_string ++ ")"
| (User n []) := n~>toSMT
| (User n xs) := "(" ++ n~>toSMT ++ " " ++ list.withSep toSMT " " xs ++ ")"

meta def ofExpr : expr → tactic Sort
| mk_Prop                    := return Bool
| (const `Int [])            := return Int
| (const `Real [])           := return Real
| (app (const `BitVec []) e) := do n ← exprToNat e, return $ BitVec n
| e                          := match get_app_fn e with
                                | (local_const _ n _ _) := do args ← mapM ofExpr (get_app_args e), return $ User n args
                                | f                     := fail $ "Sort '" ++ e~>to_string ++ "' not understood by SMT"
                                end

end Sort

-- (declare-sort List 1)
inductive SortDecl : Type
| mk : name → ℕ → SortDecl

namespace SortDecl

instance : inhabited SortDecl := ⟨⟨`_errorSortDecl, 0⟩⟩

meta def toSMT : SortDecl → string
| (mk n k) := n~>toSMT ++ " " ++ k~>to_string

meta def ofExprCore (sortName : name) : expr → nat → tactic SortDecl
| (pi _ _ mk_Type b)  k := ofExprCore b (succ k)
| mk_Type             k := return $ ⟨sortName, k⟩
| e                   _ := fail $ "SortDecl '" ++ e~>to_string ++ "' not understood by SMT"

meta def ofExpr (n : name) (e : expr) : tactic SortDecl := ofExprCore n e 0

end SortDecl

-- (declare-fun f (Int Real) Bool)
inductive FunDecl : Type
| mk : name → list Sort → Sort → FunDecl

namespace FunDecl

instance : inhabited FunDecl := ⟨⟨`_errorFunDecl, [], default Sort⟩⟩

meta def toSMT : FunDecl → string
| (mk n xs x) := n~>toSMT ++ " (" ++ list.withSep Sort.toSMT " " xs ++ ") " ++ Sort.toSMT x

meta def ofExprCore : expr →  tactic (list Sort × Sort)
| (pi _ _ dom bod) := do (xs, x) ← ofExprCore bod,
                         d ← Sort.ofExpr dom,
                         return (d :: xs, x)
| bod              := do b ← Sort.ofExpr bod,
                         return ([], b)

meta def ofExpr (funName : name) (e : expr) : tactic FunDecl :=
do (xs, x) ← ofExprCore e,
   return ⟨funName, xs, x⟩

end FunDecl

-- Terms

namespace Term

inductive Nullary : Type
| true, false

namespace Nullary
meta def toSMT : Nullary → string
| true := "true"
| false := "false"

end Nullary

inductive Unary : Type
| not
| neg, abs

namespace Unary
meta def toSMT : Unary → string
| not      := "not"
| neg      := "-"
| abs      := "abs"
end Unary

inductive Binary : Type
| eq, and, or, xor, implies
| add, sub, mul, idiv, mod, div, lt, le
| bvadd, bvmul

namespace Binary
meta def toSMT : Binary → string
| and     := "and"
| or      := "or"
| xor     := "xor"
| implies := "=>"
| eq      := "="
| add     := "+"
| sub     := "-"
| mul     := "*"
| idiv    := "div"
| mod     := "mod"
| div     := "/"
| lt      := "<"
| le      := "<="
| bvadd   := "bvadd"
| bvmul   := "bvmul"
end Binary

inductive Ternary : Type
| ite

namespace Ternary
meta def toSMT : Ternary → string
| ite     := "ite"
end Ternary

end Term

inductive SortedVar : Type
| mk : name → Sort → SortedVar

namespace SortedVar

meta def toSMT : SortedVar → string
| ⟨n, s⟩ := "(" ++ n~>toSMT ++ " " ++ s~>toSMT ++ ")"

end SortedVar

inductive Term : Type
| nullary : Term.Nullary → Term
| unary   : Term.Unary → Term → Term
| binary  : Term.Binary → Term → Term → Term
| ternary : Term.Ternary → Term → Term → Term → Term
| num     : nat → Term
| bvnum   : nat → nat → Term
| user    : name → list Term → Term
| tlet    : list (prod name Term) → Term → Term
| tforall : list SortedVar → Term → Term
| texists : list SortedVar → Term → Term

namespace Term

instance : inhabited Term := ⟨user `_errorTerm []⟩

meta def toSMT : Term → string
| (nullary c)          := c~>toSMT
| (unary c t)          := "(" ++ c~>toSMT ++ " " ++ toSMT t ++ ")"
| (binary c t₁ t₂)     := "(" ++ c~>toSMT ++ " " ++ toSMT t₁ ++ " " ++ toSMT t₂ ++ ")"
| (ternary c t₁ t₂ t₃) := "(" ++ c~>toSMT ++ " " ++ toSMT t₁ ++ " " ++ toSMT t₂ ++ " " ++ toSMT t₃ ++ ")"
| (num k)              := k~>to_string
| (bvnum k n)          := "(_ bv" ++ k~>to_string ++ " " ++ n~>to_string ++ ")"
| (user c [])          := c~>toSMT
| (user c ts)          := "(" ++ c~>toSMT ++ " " ++ list.withSep toSMT " " ts ++ ")"
-- TODO(dhs): triggers compiler issue
| (tlet vars t)        := "<let not supported yet>"
/-| (tlet vars t)    := "(let (" ++ list.withSep
                                    (λ (nt : prod name Term), nt~>fst~>to_string ++ " " ++ toSMT nt~>snd)
                                    " " vars ++ ") " ++ toSMT t ++ ")"
-/
| (tforall vars t)     := "(forall (" ++ list.withSep SortedVar.toSMT " " vars ++ ") " ++ toSMT t ++ ")"
| (texists vars t)     := "(exists (" ++ list.withSep SortedVar.toSMT " " vars ++ ") " ++ toSMT t ++ ")"

meta def ofExpr : expr → tactic Term
-- Core
| (const `true [])                  := return $ nullary Nullary.true
| (const `false [])                 := return $ nullary Nullary.false

| (app (const `not []) e)           := do t ← ofExpr e, return $ unary Unary.not t

| (app (app (app (const `eq [level.one]) _) e₁) e₂) :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.eq t₁ t₂

| (app (app (app (const `ne [level.one]) _) e₁) e₂) :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ unary Unary.not (binary Binary.eq t₁ t₂)

| (app (app (app (app (app (const `ite [level.one]) cond) _) _) e₁) e₂) :=
       do t ← ofExpr cond, t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ ternary Ternary.ite t t₁ t₂

| (app (app (const `and []) e₁) e₂) :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.and t₁ t₂
| (app (app (const `or []) e₁) e₂)  :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.or t₁ t₂
| (app (app (const `xor []) e₁) e₂)  :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.xor t₁ t₂
| (app (app (const `implies []) e₁) e₂)  :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.implies t₁ t₂

-- Int
| (const `Int.zero [])                   := return $ num 0
| (const `Int.one [])                    := return $ num 1

| (app (const `Int.neg []) e)  :=  do t ← ofExpr e, return $ unary Unary.neg t
| (app (const `Int.abs []) e)  :=  do t ← ofExpr e, return $ unary Unary.abs t

| (app (app (const `Int.add []) e₁) e₂) :=  do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.add t₁ t₂
| (app (app (const `Int.mul []) e₁) e₂) :=  do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.mul t₁ t₂
| (app (app (const `Int.sub []) e₁) e₂) :=  do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.sub t₁ t₂
| (app (app (const `Int.div []) e₁) e₂) :=  do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.idiv t₁ t₂
| (app (app (const `Int.mod []) e₁) e₂) :=  do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.mod t₁ t₂
| (app (app (const `Int.lt []) e₁) e₂)  :=  do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.lt t₁ t₂
| (app (app (const `Int.le []) e₁) e₂)  :=  do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.le t₁ t₂

-- Real
| (const `Real.zero [])                   := return $ num 0
| (const `Real.one [])                    := return $ num 1

| (app (const `Real.neg []) e)  :=  do t ← ofExpr e, return $ unary Unary.neg t
| (app (const `Real.abs []) e)  :=  do t ← ofExpr e, return $ unary Unary.abs t

| (app (app (const `Real.add []) e₁) e₂) :=  do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.add t₁ t₂
| (app (app (const `Real.mul []) e₁) e₂) :=  do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.mul t₁ t₂
| (app (app (const `Real.sub []) e₁) e₂) :=  do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.sub t₁ t₂
| (app (app (const `Real.div []) e₁) e₂) :=  do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.div t₁ t₂
| (app (app (const `Real.lt []) e₁) e₂)  :=  do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.lt t₁ t₂
| (app (app (const `Real.le []) e₁) e₂)  :=  do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.le t₁ t₂

-- BitVec
| (app (const `BitVec.zero []) e) := do n ← exprToNat e, return $ bvnum 0 n
| (app (const `BitVec.one []) e)  := do n ← exprToNat e, return $ bvnum 1 n

| (app (app (app (const `BitVec.add []) _) e₁) e₂) :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.bvadd t₁ t₂
| (app (app (app (const `BitVec.mul []) _) e₁) e₂) :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.bvmul t₁ t₂

-- FOL
| (app (app (const `Exists [level.one]) dom) bod) :=
       do uniqName ← mk_fresh_name,
          uniqId   ← mkFreshNat,
          ppName  ← return ∘ mk_simple_name $ "x_" ++ uniqId~>to_string,
          l ← return $ local_const uniqName ppName binder_info.default dom,
          t ← whnf (app bod l) >>= ofExpr,
          d ← Sort.ofExpr dom,
          return $ texists [⟨ppName, d⟩] t

| (pi n bi dom bod) := do domType ← infer_type dom,
                          domTypeIsProp ← (is_def_eq domType mk_Prop >> return tt) <|> return ff,
                          when (domTypeIsProp ∧ has_var bod) $ fail "SMT does not support dependent implications",
                          if domTypeIsProp
                          then do t₁ ← ofExpr dom, t₂ ← ofExpr bod, return $ binary Binary.implies t₁ t₂
                          else do uniqName ← mk_fresh_name,
                                  l ← return $ local_const uniqName n bi dom,
                                  t ← ofExpr $ instantiate_var bod l,
                                  d ← Sort.ofExpr dom,
                                  return $ tforall [⟨n, d⟩] t

-- Let
| (elet n t v b) := do varVal ← ofExpr v,
                       uniqName ← mk_fresh_name,
                       l ← return $ local_const uniqName n binder_info.default t,
                       body ← ofExpr $ instantiate_var b l,
                       return $ tlet [⟨n, varVal⟩] body

-- Rest
| e := -- TODO(dhs): numeral macros for Int, Real, and BitVec
       match get_app_fn_args e with
       | (local_const _ userName _ _, args) := do ts ← mapM ofExpr args, return $ user userName ts
       | _                                  := fail $ "Cannot construct SMT term from expr '" ++ e~>to_string ++ "'"
       end

end Term

inductive Command : Type
| declareSort : SortDecl → Command
| declareFun  : FunDecl → Command
| defineFun  : FunDecl → Term → Command
| assert      : Term → Command
| checkSAT    : Command

namespace Command

meta def toSMT : Command -> string
| (declareSort sortDecl) := "(declare-sort " ++ sortDecl~>toSMT ++ ")"
| (declareFun funDecl)   := "(declare-fun " ++ funDecl~>toSMT ++ ")"
| (defineFun funDecl t)  := "(define-fun " ++ funDecl~>toSMT ++ " " ++ t~>toSMT ++ ")"
| (assert t)             := "(assert " ++ t~>toSMT ++ ")"
| checkSAT               := "(check-sat)"

open tactic

meta def ofHypothesis (hyp : expr) : tactic Command :=
do hypName ← return $ lref.getPPName hyp,
   hypType ← lref.getType hyp,
   hypValue ← lref.getValue hyp,
   hypTypeType ← infer_type hypType,

--   trace (hypName, hypType, hypTypeType),
   match hypTypeType with
   | mk_Prop  := do t ← Term.ofExpr hypType, return $ assert t
   | mk_Type  := match hypValue with
                 | none   := do funDecl ← FunDecl.ofExpr hypName hypType, return $ declareFun funDecl
                 | some v := do t ← Term.ofExpr v, funDecl ← FunDecl.ofExpr hypName hypType, return $ defineFun funDecl t
                 end
   | mk_Type₂ := do sortDecl ← SortDecl.ofExpr hypName hypType, return $ declareSort sortDecl
   | _        := fail $ "unexpected Type of hypothesis: " ++ expr.to_string hypType
   end

end Command

-- TODO(dhs): note that there are many places that need to be updated when the supported theory constants change
private meta def theoryNames : rb_map name unit :=
let names : list name :=
    [`Exists,
     `Int, `Real, `BitVec,
     `true, `false, `and, `or, `not, `xor, `implies, `eq, `ite,
     `ne, -- It is not in the SMT theory directly, but we handle it in Term.ofExpr for convenience
     `Int.zero, `Int.one, `Int.neg, `Int.abs, `Int.add, `Int.mul, `Int.div, `Int.sub, `Int.mod, `Int.le, `Int.lt,
     `Real.zero, `Real.one, `Real.neg, `Real.add, `Real.mul, `Real.div, `Real.sub, `Real.le, `Real.lt,
     `BitVec.zero, `BitVec.one, `BitVec.add, `BitVec.mul
     ] in
rb_map.of_list (list.zip names (list.repeat () $ list.length names))

meta def isTheoryName (n : name) : bool := theoryNames~>contains n

meta def Z3Core : tactic unit :=
do hyps  ← local_context,
   tgt   ← target,
   guard (tgt = expr.const `false []),
   cmds ← mapM Command.ofHypothesis hyps,
   cmdString ← return $ list.withSep Command.toSMT " " (cmds ++ [Command.checkSAT]),
   trace cmdString,
   result ← callZ3 cmdString,
   trace result,
   if result = "unsat\n" then trustZ3 tgt >>= exact else fail ("Z3: " ++ result)

end smt
end tactic


/-
Notes:

1. A lot of design freedom for how much is done in the pre-processing vs the (essentially-atomic) end-game tactic
   - type classes?
     + right now we assume everything is left in terms of add, mul, etc., even for bitvectors
   - by contradiction?
     + right now we don't handle this
   - intros?
     + right now we call intros
   - P -> Q ==> implies P Q?
     + right now we don't handle this, but do handle `→` directly as the smt "=>"

2. We need to escape strings
   - no unicode
   - no '
   - no .
   - (check smtlib)

3. Flatten n-ary operators (and let/forall/exists variables) in Term.ofExpr?
   - May want to wait until mutual definitions for this

4. Let
   - compiler still crashing
   - even if it worked, how to access local context from Lean?

5. Nat
   - Right now I am not handling ℕ at all, only Int and Real
   - I am assuming there will be an entire pass devoted to ℕ → Int, where
     + (x : nat) ==> (x : Int) (H : x >= 0)
     + (f : X -> nat) ==> (f : X → Int) (H : ∀ x, f x >= 0)
     + (f : nat -> X) ==> (f : int → X),
       and all lemmas involving f take (H : x ≥ 0) as a precondition whenever (f x) appears
       (this is the trickier one)

6. General issue, that merits waiting until the bitvector library is actually developed
   - What types will the lean BitVec operators have?

Main extensions:

1. Collect constants that appear in the goal
   - Declare them (Sorts / Funs)
   - For functions: optionally include their defining equations, or just their definitions, as lemmas
     + this will introduce new constants and the cycle will need to repeat, perhaps with some depth-cutoff
     + since there are ordering dependencies, I see this as a probable StateT <stuff> tactic computation
   - Next level: relevancy filter for finding other lemmas to include

2. Generic subtype handling?


3. Generic dependent types handling, with a HasType predicate?
   - Way out of scope for now

-/
