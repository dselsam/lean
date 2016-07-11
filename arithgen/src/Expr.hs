module Expr where

data Expr = Add [Expr]
    | Mul [Expr]
    | Var Int
    | Num Int deriving (Eq, Show, Ord)
