module Render where

import Expr

{-
data Expr = Add [Expr]
    | Mul [Expr]
    | Var Int
    | Num Int deriving (Eq, Show, Ord)
-}

leanHeader numVars = "import algebra.ring\nset_option unifier.conservative true\n"
                     ++ "set_option unifier.max_steps 1000000\n"
                     ++ "namespace tactic\n"
                     ++ "meta_constant arith_normalize : expr → tactic (prod expr expr)\n"
                     ++ "meta_definition arith : tactic unit := do (new_target, Heq) ← target >>= arith_normalize, assert \"Htarget\" new_target, reflexivity, Ht ← get_local \"Htarget\", mk_app (\"eq\" <.> \"mpr\") [Heq, Ht] >>= exact\n"
                     ++ "end tactic\n"
                     ++ "open tactic\n"
                     ++ "constants (X : Type.{1}) (X_inst : comm_ring X) (X_add : has_add X) (X_mul : has_mul X)\nattribute X_inst [instance]\n"
                     ++ "constants (" ++ concatMap (\i -> exprToLean (Var i) ++ " ") [1..numVars] ++ " : X)\n"

exprToLean (Add es) = foldr (\e s -> "(@add.{1} X X_add " ++ exprToLean e ++ " " ++ s ++ ")") (exprToLean (last es)) (init es)
exprToLean (Mul es) = foldr (\e s -> "(@mul.{1} X X_mul " ++ exprToLean e ++ " " ++ s ++ ")") (exprToLean (last es)) (init es)
exprToLean (Var i) = "x" ++ show i
exprToLean (Num i) = "(" ++ show i ++ ")"

exprToLeanCmd numVars e = leanHeader numVars ++ "#fast_arith_normalize " ++ exprToLean e
