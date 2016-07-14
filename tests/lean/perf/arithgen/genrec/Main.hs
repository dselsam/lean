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
  [numVars, maxPerAdd, maxPerMul, maxCoeff, bottomWeight] <- getArgs
  e <- evalRandIO $ genRecExpr (read numVars) (read maxPerAdd) (read maxPerMul) (read maxCoeff) (fromIntegral . read $ bottomWeight)
  writeFile "genrec1.smt2" $ exprToZ3Assert (read numVars) e
  writeFile "genrec1.lean" $ exprToLeanExample (read numVars) e
