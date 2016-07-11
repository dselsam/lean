module Main where

import Expr
import Gen
import Render

import System.Environment
import Control.Monad
import Control.Monad.Random (evalRandIO)

main :: IO ()
main = do
  [numVars, maxPerAdd, maxPerMul, maxCoeff, recurseWeight] <- getArgs
  e <- evalRandIO $ genExpr (read numVars) (read maxPerAdd) (read maxPerMul) (read maxCoeff) (fromIntegral . read $ recurseWeight)
  putStrLn $ exprToLeanCmd (read numVars) e
