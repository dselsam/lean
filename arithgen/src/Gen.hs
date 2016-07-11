module Gen where

import qualified Control.Monad.Random as Random
import Control.Monad.Random (Rand, RandomGen)

import Expr

genExpr :: (RandomGen g) => Int -> Int -> Int -> Int -> Rational -> Rand g Expr
genExpr numVars maxPerAdd maxPerMul maxCoeff recurseWeight = genAdd numVars maxPerAdd maxPerMul maxCoeff recurseWeight
    where
      genAdd :: (RandomGen g) => Int -> Int -> Int -> Int -> Rational -> Rand g Expr
      genAdd numVars maxPerAdd maxPerMul maxCoeff recurseWeight = do
        numSummands <- Random.uniform [1..maxPerAdd]
        summands <- mapM (\_ -> genMul numVars maxPerAdd maxPerMul maxCoeff recurseWeight) [1..numSummands]
        return $ Add summands

      genMul :: (RandomGen g) => Int -> Int -> Int -> Int -> Rational -> Rand g Expr
      genMul numVars maxPerAdd maxPerMul maxCoeff recurseWeight = do
        numSummands <- Random.uniform [1..maxPerMul]
        recurses <- mapM (\_ -> Random.fromList [(True, recurseWeight), (False, 1)]) [1..numSummands]
        summands <- mapM (\i -> if recurses!!(i-1) then genLeaf numVars maxCoeff else genAdd numVars maxPerAdd maxPerMul maxCoeff recurseWeight) [1..numSummands]
        return $ Mul summands

      genLeaf :: (RandomGen g) => Int -> Int -> Rand g Expr
      genLeaf numVars maxCoeff = do
                            var <- Random.uniform [1..numVars]
                            coeff <- Random.uniform [-maxCoeff..maxCoeff]
                            return $ Mul [Var var, Num coeff]
