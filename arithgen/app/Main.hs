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
  [numVars, maxPerAdd, maxPerMul, maxCoeff, recurseWeight] <- getArgs
  e <- evalRandIO $ genExpr (read numVars) (read maxPerAdd) (read maxPerMul) (read maxCoeff) (fromIntegral . read $ recurseWeight)
  writeFile "rand1.smt2" $ exprToZ3Assert (read numVars) e
  writeFile "rand1.lean" $ exprToLeanExample (read numVars) e
