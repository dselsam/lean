module Gen where

import qualified Control.Monad.Random as Random
import Control.Monad.Random (Rand, RandomGen)

import Expr

genExpr :: (RandomGen g) => Int -> Int -> Int -> Int -> Rational -> Rand g Expr
genExpr numVars maxPerAdd maxPerMul maxCoeff bottomWeight = genAdd numVars maxPerAdd maxPerMul maxCoeff bottomWeight
    where
      genAdd :: (RandomGen g) => Int -> Int -> Int -> Int -> Rational -> Rand g Expr
      genAdd numVars maxPerAdd maxPerMul maxCoeff bottomWeight = do
        numSummands <- Random.uniform [1..maxPerAdd]
        summands <- mapM (\_ -> genMul numVars maxPerAdd maxPerMul maxCoeff bottomWeight) [1..numSummands]
        return $ Add summands

      genMul :: (RandomGen g) => Int -> Int -> Int -> Int -> Rational -> Rand g Expr
      genMul numVars maxPerAdd maxPerMul maxCoeff bottomWeight = do
        numSummands <- Random.uniform [1..maxPerMul]
        bottoms <- mapM (\_ -> Random.fromList [(True, bottomWeight), (False, 1)]) [1..numSummands]
        summands <- mapM (\i -> if bottoms!!(i-1) then genLeaf numVars maxCoeff else genAdd numVars maxPerAdd maxPerMul maxCoeff bottomWeight) [1..numSummands]
        return $ Mul summands

      genLeaf :: (RandomGen g) => Int -> Int -> Rand g Expr
      genLeaf numVars maxCoeff = do
                            var <- Random.uniform [1..numVars]
                            coeff <- Random.uniform [-maxCoeff..maxCoeff]
                            if var == numVars then return (Num (fromIntegral coeff)) else return (Mul [Var var, Num (fromIntegral coeff)])
