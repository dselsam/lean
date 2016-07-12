module Expr where

data Expr = Add [Expr]
    | Mul [Expr]
    | Var Int
    | Num Integer deriving (Eq, Show, Ord)
