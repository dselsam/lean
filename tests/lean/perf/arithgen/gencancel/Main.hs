module Main where

import Expr
import Gen
import RenderLean
import RenderZ3

import System.Environment
import Control.Monad
import Control.Monad.Random (evalRandIO)

main :: IO ()
main = do
  [numToCancel] <- getArgs
  let e = genCancelExpr (read numToCancel)
  writeFile "gencancel1.smt2" $ exprToZ3Assert2 (read numToCancel) e e
  writeFile "gencancel1.lean" $ exprToLeanExample2 (read numToCancel) e e
