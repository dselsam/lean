module RenderLean where

import Expr
import Norm

leanHeader numVars = "import algebra.ring\n"
                     ++ "import algebra.arith_util\n"
                     ++ "set_option unifier.conservative true\n"
                     ++ "set_option unifier.max_steps 1000000\n"
                     ++ "namespace tactic\n"
                     ++ "meta_constant arith_normalize : expr → tactic (prod expr expr)\n"
                     ++ "meta_definition arith : tactic unit := do (new_target, Heq) ← target >>= arith_normalize, assert \"Htarget\" new_target, reflexivity, Ht ← get_local \"Htarget\", mk_app (\"eq\" <.> \"mpr\") [Heq, Ht] >>= exact\n"
                     ++ "end tactic\n"
                     ++ "open tactic\n"
                     ++ "open tactic\n"
                     ++ "constants (X : Type.{1}) (X_cr : comm_ring X) (X_add : has_add X) (X_mul : has_mul X) (X_one : has_one X) (X_zero : has_zero X) (X_neg : has_neg X)\n"
                     ++ "attribute X_cr [instance]\n"
                     ++ "constants (" ++ concatMap (\i -> exprToLean (Var i) ++ " ") [1..numVars] ++ " : X)\n"
                     ++ "set_option arith_normalizer.distribute_mul true\n"
                     ++ "set_option arith_normalizer.profile true\n"


numToLean k
    | k < 0 = mkNeg (-k)
    | k == 0 = mkZero
    | k == 1 = mkOne
    | True = if rem k 2 == 0 then mkBit0 (div k 2) else mkBit1 (div k 2)
    where
      mkZero = "(@zero.{1} X X_zero)"
      mkOne = "(@one.{1} X X_one)"
      mkNeg k = "(@neg.{1} X X_neg " ++ numToLean k ++ ")"
      mkBit0 k = "(@bit0.{1} X X_add " ++ numToLean k ++ ")"
      mkBit1 k = "(@bit1.{1} X X_one X_add " ++ numToLean k ++ ")"

exprToLean (Add es) = foldr (\e s -> "(@add.{1} X X_add " ++ exprToLean e ++ " " ++ s ++ ")") (exprToLean (last es)) (init es)
exprToLean (Mul es) = foldr (\e s -> "(@mul.{1} X X_mul " ++ exprToLean e ++ " " ++ s ++ ")") (exprToLean (last es)) (init es)
exprToLean (Var i) = "x" ++ show i
exprToLean (Num i) = numToLean i

exprToLeanCmd numVars e = leanHeader numVars ++ "#fast_arith_normalize " ++ exprToLean e

exprToLeanExample numVars e = leanHeader numVars ++ "example : @eq.{1} X (" ++ exprToLean e ++ ") (" ++ exprToLean (normalize e) ++ ") := by arith"
