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
  [numToFuse] <- getArgs
  let e = genFuseExpr (read numToFuse)
  writeFile "genfuse1.smt2" $ exprToZ3Assert 1 e
  writeFile "genfuse1_bin.smt2" $ exprToZ3Assert_bin 1 e
  writeFile "genfuse1.lean" $ exprToLeanExample 1 e
