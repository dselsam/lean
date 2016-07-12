module RenderZ3 where

import Expr
import Norm

z3Vars :: Int -> String
z3Vars n | n == 0 = ""
         | n > 0 = "(declare-const x" ++ show n ++ " Int)\n" ++ z3Vars (n-1)

z3Header numVars = z3Vars numVars

exprToZ3 :: Expr -> String
exprToZ3 (Add es) = "(+ " ++ concatMap (\e -> " " ++ exprToZ3 e ++ " ") es ++ ")"
exprToZ3 (Mul es) = "(* " ++ concatMap (\e -> " " ++ exprToZ3 e ++ " ") es ++ ")"
exprToZ3 (Var j) = "x" ++ show j
exprToZ3 (Num i) = show i

assertNotEqZ3 :: Expr -> Expr -> String
assertNotEqZ3 lhs rhs = "(assert (not (= " ++ exprToZ3 lhs ++ " " ++ exprToZ3 rhs ++ ")))"

exprToZ3Assert :: Int -> Expr -> String
exprToZ3Assert numVars e = z3Header numVars ++ assertNotEqZ3 e (normalize e) ++ "(check-sat)"
