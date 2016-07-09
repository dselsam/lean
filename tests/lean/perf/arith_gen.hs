import System.Environment
import Control.Monad

class Problem p where
    toZ3 :: p -> String
    toLean :: p -> String

-- [(1, 3), (2, 4)] means 1 * x3 + 2 * x4
type Monomial = (Int, Int)
type Polynomial = [Monomial]

data Problem1 = Problem1 {
     numVars1 :: Int,
     lhs1 :: Polynomial,
     rhs1 :: Polynomial
}

genProblem1 :: Int -> Int -> Int -> Problem1
genProblem1 numVars numRepeats scale =
    -- (x_1 + .. + x_numVars) + ... = numRepeats * x_1 + ... numRepeats * x_numVars
    let vars = [1..numVars]
        lhs = concat $ replicate numRepeats (map (\var -> (scale, var)) vars)
        rhs = map (\var -> (numRepeats * scale, var)) vars
    in
      Problem1 numVars lhs rhs

z3Vars :: Int -> String
z3Vars n | n == 0 = ""
         | n > 0 = "(declare-const x" ++ show n ++ " Int)\n" ++ z3Vars (n-1)

mkVar v = "x" ++ show v

polyToZ3 :: Polynomial -> String
polyToZ3 ms = "(+ " ++ concatMap monoToZ3 ms ++ ")"
    where
      monoToZ3 (c, v) = "(* " ++ show c ++ " " ++ mkVar v ++ ") "

assertNotEqZ3 :: Polynomial -> Polynomial -> String
assertNotEqZ3 lhs rhs = "(assert (not (= " ++ polyToZ3 lhs ++ " " ++ polyToZ3 rhs ++ ")))"

problem1ToZ3 :: Problem1 -> String
problem1ToZ3 (Problem1 numVars lhs rhs) = z3Vars numVars ++ assertNotEqZ3 lhs rhs ++ "(check-sat)"


leanHeader = "import algebra.ring\nset_option unifier.conservative true\nset_option unifier.max_steps 1000000\nnamespace tactic\nmeta_constant arith_normalize : expr → tactic (prod expr expr)\nmeta_definition arith : tactic unit := do (new_target, Heq) ← target >>= arith_normalize, assert \"Htarget\" new_target, reflexivity, Ht ← get_local \"Htarget\", mk_app (\"eq\" <.> \"mpr\") [Heq, Ht] >>= exact\nend tactic\nopen tactic\nconstants (X : Type.{1}) (X_inst : comm_ring X) (X_add : has_add X) (X_mul : has_mul X)\nattribute X_inst [instance]\n"

leanVars n = "constants (" ++ concatMap (\i -> mkVar i ++ " ") [1..n] ++ " : X)\n"

exampleEqLean :: Polynomial -> Polynomial -> String
exampleEqLean lhs rhs = "example : " ++ polyToLean lhs ++ " = " ++ polyToLean rhs ++ " := by arith"

polyToLean ms = let mons = map (\(c, v) -> "(@mul X X_mul (" ++ show c ++ ") " ++ mkVar v ++ ")") ms
                    mkAdd mon soFar = "(@add X X_add " ++ mon ++ " " ++ soFar ++ ")"
                in
                  foldr mkAdd (last mons) (init mons)

problem1ToLean :: Problem1 -> String
problem1ToLean (Problem1 numVars lhs rhs) =
    leanHeader ++ leanVars numVars ++ exampleEqLean lhs rhs

instance Problem Problem1 where
    toZ3 = problem1ToZ3
    toLean = problem1ToLean

-- RHS = 0
data Problem2 = Problem2 {
     numVars2 :: Int,
     lhs2 :: Polynomial
}

problem2ToLean :: Problem2 -> String
problem2ToLean (Problem2 numVars lhs) = leanHeader ++ leanVars numVars ++ "example : " ++ polyToLean lhs ++ " = 0 := by arith"

genProblem2 :: Int -> Int -> Int -> Problem2
genProblem2 numVars numRepeats scale =
    -- (x_1 + .. + x_numVars) + ... +  (- numRepeats) * x_1 + ... + (- numRepeats) * x_numVars
    let vars = [1..numVars]
        lhs = concat $ replicate numRepeats (map (\var -> (scale, var)) vars)
        rhs = map (\var -> (- numRepeats * scale, var)) vars
    in
      Problem2 numVars (lhs ++ rhs)

problem2ToZ3 :: Problem2 -> String
problem2ToZ3 (Problem2 numVars lhs) = z3Vars numVars ++ "(assert (not (= " ++ polyToZ3 lhs ++ " 0)))\n" ++ "(check-sat)"

instance Problem Problem2 where
    toZ3 = problem2ToZ3
    toLean = problem2ToLean

main = do
  [numVars, numRepeats, scale] <- getArgs
  let p1 = genProblem1 (read numVars) (read numRepeats) (read scale)
  writeFile "arith1.smt2" $ toZ3 p1
  writeFile "arith1.lean" $ toLean p1

  let p2 = genProblem2 (read numVars) (read numRepeats) (read scale)
  writeFile "arith2.smt2" $ toZ3 p2
  writeFile "arith2.lean" $ toLean p2
