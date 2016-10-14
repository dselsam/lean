/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
-- Arith
constants (Int Real : Type)

instance : has_zero Int := sorry
instance : has_one Int := sorry
instance : has_add Int := sorry
instance : has_mul Int := sorry
instance : has_lt Int := sorry

instance : has_zero Real := sorry
instance : has_one Real := sorry
instance : has_add Real := sorry
instance : has_mul Real := sorry
instance : has_lt Real := sorry

-- Bit vectors

constants (BitVec : ℕ → Type)

instance (n : ℕ) : has_zero (BitVec n) := sorry
instance (n : ℕ) : has_one (BitVec n) := sorry
instance (n : ℕ) : has_add (BitVec n) := sorry
instance (n : ℕ) : has_mul (BitVec n) := sorry

set_option pp.all true
set_option eqn_compiler.max_steps 10000

namespace Util

private def list.withSepCore {X : Type} (f : X -> string) (sep : string) : bool -> list X -> string
| b [] := ""
| tt (x::xs) := f x ++ list.withSepCore ff xs
| ff (x::xs) := sep ++ f x ++ list.withSepCore ff xs

def list.withSep {X : Type} (f : X -> string) (sep : string) : list X -> string := list.withSepCore f sep tt

end Util

open Util

namespace name

-- TODO(dhs): will need to get rid of unicode, and do other things as well
def toSMT : name → string
| anonymous                := "[anonymous]"
| (mk_string s anonymous)  := s
| (mk_numeral v anonymous) := v~>val~>to_string
| (mk_string s n)          := toSMT n ++ "__" ++ s
| (mk_numeral v n)         := toSMT n ++ "__" ++ v~>val~>to_string

end name

namespace level

@[reducible, pattern] definition one : level := succ zero
@[reducible, pattern] definition two : level := succ one

end level

namespace expr

@[reducible, pattern] meta def mk_Prop : expr := sort level.zero
@[reducible, pattern] meta def mk_Type : expr := sort level.one
@[reducible, pattern] meta def mk_Type₂ : expr := sort level.two

meta def toNat : expr → ℕ
| (app (app (const `zero _) _) _) := 0
| (app (app (const `one _)  _) _)  := 1
| (app (app (app (const `bit0 _) _) _) e) := 2 * toNat e
| (app (app (app (app (const `bit1 _) _) _) _) e) := 2 * (toNat e) + 1
| _ := 0 -- ERROR

meta def toMaybeNat : expr → option (ℕ × expr)
| (app (app (const `zero _) ty) _) := some (0, ty)
| (app (app (const `one _)  ty) _)  := some (1, ty)
| (app (app (app (const `bit0 _) ty) _) e) := do n ← toMaybeNat e, return (2 * n~>fst, ty)
| (app (app (app (app (const `bit1 _) ty) _) _) e) := do n ← toMaybeNat e, return $ (2 * n~>fst + 1, ty)
| _ := none

end expr

namespace tactic

-- TODO(dhs): cheap trick to avoid needing to either write C++ or use a gensym monad transformer
meta def mk_fresh_nat : tactic ℕ :=
do (name.mk_numeral k _) ← mk_fresh_name | failed,
   return k~>val

namespace smt

meta constant trustZ3 : expr -> tactic expr
meta constant callZ3 : string -> tactic string

open expr nat

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

meta def ofExpr : expr → Sort
| mk_Prop                    := Bool
| (const `Int [])            := Int
| (const `Real [])           := Real
| (app (const `BitVec []) e) := BitVec (toNat e)
| e                          := match get_app_fn e with
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
| (mk n k) := n~>toSMT ++ " " ++ k~>to_string

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
| (mk n xs x) := n~>toSMT ++ " (" ++ list.withSep Sort.toSMT " " xs ++ ") " ++ Sort.toSMT x

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

namespace Nullary
meta def toSMT : Nullary → string
| true := "true"
| false := "false"

end Nullary

inductive Unary : Type
| not
| uminus, abs --, to_Real, to_Int, is_Int

namespace Unary
meta def toSMT : Unary → string
| not     := "not"
| uminus  := "-"
| abs     := "abs"
end Unary

inductive Binary : Type
| and, or, eq, implies
| plus, sub, times, idiv, mod, div, lt, le, gt, ge
| bvadd, bvmul

namespace Binary
meta def toSMT : Binary → string
| and     := "and"
| or      := "or"
| implies := "=>"
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
| bvadd   := "bvadd"
| bvmul   := "bvmul"
end Binary

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
| num     : nat → Term
| bvnum   : nat → nat → Term
| user    : name → list Term → Term
| tlet    : list (prod name Term) → Term → Term
| tforall : list SortedVar → Term → Term
| texists : list SortedVar → Term → Term

namespace Term

instance : inhabited Term := ⟨user `_errorTerm []⟩

meta def toSMT : Term → string
| (nullary c)      := c~>toSMT
| (unary c t)      := "(" ++ c~>toSMT ++ " " ++ toSMT t ++ ")"
| (binary c t₁ t₂) := "(" ++ c~>toSMT ++ " " ++ toSMT t₁ ++ " " ++ toSMT t₂ ++ ")"
| (num k)          := k~>to_string
| (bvnum k n)      := "(_ bv" ++ k~>to_string ++ " " ++ n~>to_string ++ ")"
| (user c [])      := c~>toSMT
| (user c ts)      := "(" ++ c~>toSMT ++ " " ++ list.withSep toSMT " " ts ++ ")"
-- TODO(dhs): factoring out this lambda triggers compiler issue
| (tlet vars t)    := "<let not supported yet>"
/-| (tlet vars t)    := "(let (" ++ list.withSep
                                    (λ (nt : prod name Term), nt~>fst~>to_string ++ " " ++ toSMT nt~>snd)
                                    " " vars ++ ") " ++ toSMT t ++ ")"
-/
| (tforall vars t) := "(forall (" ++ list.withSep SortedVar.toSMT " " vars ++ ") " ++ toSMT t ++ ")"
| (texists vars t) := "(exists (" ++ list.withSep SortedVar.toSMT " " vars ++ ") " ++ toSMT t ++ ")"

meta def ofExpr : expr → tactic Term
| (const `true [])                  := return $ nullary Nullary.true
| (const `false [])                 := return $ nullary Nullary.false

| (app (const `not []) e)           := do t ← ofExpr e, return $ unary Unary.not t
| (app (const `neg []) e)           := do t ← ofExpr e, return $ unary Unary.uminus t
| (app (const `abs []) e)           := do t ← ofExpr e, return $ unary Unary.abs t

| (app (app (app (const `eq ls) _) e₁) e₂) :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.eq t₁ t₂
| (app (app (app (const `ne ls) _) e₁) e₂) :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ unary Unary.not (binary Binary.eq t₁ t₂)

| (app (app (const `and []) e₁) e₂) :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.and t₁ t₂
| (app (app (const `or []) e₁) e₂)  :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.or t₁ t₂

-- Arith
-- TODO(dhs): could flatten n-ary applications here
-- TODO(dhs): Do we want to strip the type class abstractions here or  during pre-processing?
| (app (app (const `zero [level.one]) (const `Int [])) _) := return $ num 0
| (app (app (const `one [level.one])  (const `Int [])) _) := return $ num 1
| (app (app (app (app (const `add [level.one]) (const `Int [])) _) e₁) e₂) :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.plus t₁ t₂
| (app (app (app (app (const `mul [level.one]) (const `Int [])) _) e₁) e₂) :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.times t₁ t₂
| (app (app (app (app (const `gt [level.one]) (const `Int [])) _) e₁) e₂) :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.gt t₁ t₂
| (app (app (app (app (const `ge [level.one]) (const `Int [])) _) e₁) e₂) :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.ge t₁ t₂
| (app (app (app (app (const `lt [level.one]) (const `Int [])) _) e₁) e₂) :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.lt t₁ t₂
| (app (app (app (app (const `le [level.one]) (const `Int [])) _) e₁) e₂) :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.le t₁ t₂

| (app (app (const `zero [level.one]) (const `Real [])) _) := return $ num 0
| (app (app (const `one [level.one])  (const `Real [])) _) := return $ num 1
| (app (app (app (app (const `add [level.one]) (const `Real [])) _) e₁) e₂) :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.plus t₁ t₂
| (app (app (app (app (const `mul [level.one]) (const `Real [])) _) e₁) e₂) :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.times t₁ t₂
| (app (app (app (app (const `gt [level.one]) (const `Real [])) _) e₁) e₂) :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.gt t₁ t₂
| (app (app (app (app (const `ge [level.one]) (const `Real [])) _) e₁) e₂) :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.ge t₁ t₂
| (app (app (app (app (const `lt [level.one]) (const `Real [])) _) e₁) e₂) :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.lt t₁ t₂
| (app (app (app (app (const `le [level.one]) (const `Real [])) _) e₁) e₂) :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.le t₁ t₂

-- BitVectors
-- TODO(dhs): spit out the dependent tags (_ bv0 <n>) (_ bv1 <n>)
| (app (app (const `zero [level.one]) (app (const `BitVec []) e)) _) := return $ bvnum 0 (toNat e)
| (app (app (const `one [level.one]) (app (const `BitVec []) e)) _) := return $ bvnum 1 (toNat e)

| (app (app (app (app (const `add [level.one]) (app (const `BitVec []) e)) _) e₁) e₂) :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.bvadd t₁ t₂
| (app (app (app (app (const `mul [level.one]) (app (const `BitVec []) e)) _) e₁) e₂) :=
       do t₁ ← ofExpr e₁, t₂ ← ofExpr e₂, return $ binary Binary.bvmul t₁ t₂

-- FOL
| (app (app (const `Exists [level.one]) dom) bod) :=
       do uniqName ← mk_fresh_name,
          uniqId   ← mk_fresh_nat,
          ppName  ← return ∘ mk_simple_name $ "x_" ++ uniqId~>to_string,
          l ← return $ local_const uniqName ppName binder_info.default dom,
          t ← whnf (app bod l) >>= ofExpr,
          return $ texists [⟨ppName, Sort.ofExpr dom⟩] t

| (pi n bi dom bod) := do domType ← infer_type dom,
                          domTypeIsProp ← (is_def_eq domType mk_Prop >> return tt) <|> return ff,
                          when (domTypeIsProp ∧ has_var bod) $ fail "no dependent implications allowed",
                          if domTypeIsProp
                          then do t₁ ← ofExpr dom, t₂ ← ofExpr bod, return $ binary Binary.implies t₁ t₂
                          else do uniqName ← mk_fresh_name,
                                  l ← return $ local_const uniqName n bi dom,
                                  t ← ofExpr $ instantiate_var bod l,
                                  return $ tforall [⟨n, Sort.ofExpr dom⟩] t

-- Let
| (elet n t v b) := do varVal ← ofExpr v,
                       uniqName ← mk_fresh_name,
                       l ← return $ local_const uniqName n binder_info.default t,
                       body ← ofExpr $ instantiate_var b l,
                       return $ tlet [⟨n, varVal⟩] body

-- Rest
| e := match toMaybeNat e with
       | some (k, const `Int []) := return $ num k
       | some (k, const `Real []) := return $ num k
       | some (k, app (const `BitVec []) e) := return $ bvnum k (toNat e) -- TODO(dhs): handle errors?
       | some _ := return $ user (mk_str_name e~>to_string "TERM_ERROR::UNEXPECTED_NUMERAL") [] -- ERROR
       | _ :=
       -- TODO(dhs): syntactically awkward
       match get_app_fn_args e with
       | (local_const _ userName _ _, args) := do ts ← monad.mapM ofExpr args, return $ user userName ts
       | _                                  := return $ user (mk_str_name e~>to_string "TERM_ERROR") [] -- ERROR
       end
       end

end Term

exit
inductive Command : Type
| declareSort : SortDecl → Command
| declareFun  : FunDecl → Command
| assert      : Term → Command
| checkSAT    : Command

namespace Command

meta def toSMT : Command -> string
| (declareSort sortDecl) := "(declare-sort " ++ sortDecl~>toSMT ++ ")"
| (declareFun funDecl)   := "(declare-fun " ++ funDecl~>toSMT ++ ")"
| (assert t)             := "(assert " ++ t~>toSMT ++ ")"
| checkSAT               := "(check-sat)"

open tactic

meta def ofHypothesis (hyp : expr) : tactic Command :=
do hypName ← return $ local_pp_name hyp,
   hypType ← infer_type hyp,
   hypTypeType ← infer_type hypType,
--   trace (hypName, hypType, hypTypeType),
   match hypTypeType with
   | mk_Prop  := do t ← Term.ofExpr hypType, return $ assert t
   | mk_Type  := return $ declareFun (FunDecl.ofExpr hypName hypType)
   | mk_Type₂ := return $ declareSort (SortDecl.ofExpr hypName hypType)
   | _        := fail $ "unexpected Type of hypothesis: " ++ expr.to_string hypType
   end

end Command


meta def Z3 : tactic unit :=
do intros,
   hyps  ← local_context,
   tgt   ← target,
   guard (tgt = expr.const `false []),
   cmds ← monad.mapM Command.ofHypothesis hyps,
   cmdString ← return $ list.withSep Command.toSMT " " (cmds ++ [Command.checkSAT]),
   trace cmdString,
   result ← callZ3 cmdString,
   trace result,
   if result = "unsat\n" then trustZ3 tgt >>= exact else fail ("Z3: " ++ result)

end smt
end tactic

namespace Examples
open tactic
open tactic.smt

-- Prop logic
--example (P : Prop) : P → P → false := by Z3 -- should FAIL
example (P : Prop) : P → ¬ P → false := by Z3
example (P Q : Prop) : P ∧ Q → ¬ P → (¬ P ∨ ¬ Q) → false := by Z3
example (P Q : Prop) : P ∧ Q → ¬ P → (¬ P → ¬ Q) → false := by Z3

-- EUF
--example (X Y : Type) (f g : X → X → Y) (x1 x1B x2 x2B : X) : x1 ≠ x1B → x2 ≠ x2B → f x1 x2 = f x1B x2B → false := by Z3 -- should FAIL
example (X Y : Type) (f g : X → X → Y) (x1 x1B x2 x2B : X) : x1 = x1B → x2 = x2B → f x1 x2 ≠ f x1B x2B → false := by Z3

-- Ints
--example (z1 z2 z3 : Int) : z1 = z2 + z3 → z2 = z1 + z3 → z3 = z1 + z2 → z1 = 0 → false := by Z3 -- should FAIL
example (z1 z2 z3 : Int) : z1 = z2 + z3 → z2 = z1 + z3 → z3 = z1 + z2 → z1 > 0 → false := by Z3
example : (∀ (n : Int), ∃ (m : Int), n * m = 1) → false := by Z3
example : (7 : Int) * 5 > 40 → false := by Z3
example : (∃ (n : Int), (7 : Int) * n = 1) → false := by Z3

-- Reals
--example (z1 z2 z3 : Real) : z1 = z2 + z3 → z2 = z1 + z3 → z3 = z1 + z2 → z1 = 0 → false := by Z3 -- should FAIL
-- example : (∀ (n : Real), n ≠ 0 → ∃ (m : Real), n * m = 1) → false := by Z3 -- should FAIL/TIMEOUT
example (z1 z2 z3 : Real) : z1 = z2 + z3 → z2 = z1 + z3 → z3 = z1 + z2 → z1 > 0 → false := by Z3
example : (7 : Real) * 5 > 40 → false := by Z3
example : (∃ (n : Real), n > 10 ∧ (7 : Real) * n = 1) → false := by Z3

-- Quantifiers
--example (X : Type) (x : X) (f g : X → X) : (∀ (x : X), f x = g x) → (∃ (x : X), f x = g x) → false := by Z3 -- should FAIL
example (X : Type) (x1 x2 : X) (f : X → X) : (∀ (x1 x2 : X), f x1 = f x2 → x1 = x2) →  f x1 = f x2 → x1 ≠ x2 → false := by Z3
example (X : Type) (x : X) (f g : X → X) : (∃ (x : X), f x = g x) → (∀ (x : X), f x ≠ g x) → false := by Z3
example (X : Type) (x1 x2 : X) : x1 ≠ x2 → (¬ ∃ (x1 x2 : X), x1 ≠ x2) → false := by Z3

-- BitVectors
example (x y z : BitVec 16) : x + x = y → y + y = z → x + x + x + x ≠ z → false := by Z3
example (x y z : BitVec 16) : 2 * x = y → 3 * y = z → 6 * x ≠ z → false := by Z3
example : (¬ ∃ (x : BitVec 16), x ≠ 0 ∧ 2 * x = 0) → false := by Z3

-- Let
-- TODO(dhs): figure out how to access local context in Lean
--example (X : Type) (x : X) (f : X → X) : (let y : X := f x in y ≠ f x) → false := by Z3
--example (X : Type) (x : X) (f : X → X) : let y : X := f x in y ≠ f x → false := by Z3


end Examples

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
