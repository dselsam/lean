module Norm where

import Expr

import Data.Map (Map)
import qualified Data.Map as Map

normalize :: Expr -> Expr
normalize e = case e of
                Add es -> normalize_add es
                Mul es -> normalize_mul es True
                _ -> e

normalize_add :: [Expr] -> Expr
normalize_add es =
    let es_n = map normalize es
        coeff = sum (map (\e -> case e of
                                  Num i -> i
                                  _ -> 0) es_n)
        pps_to_count = foldl (\m e -> case e of
                                        Num i -> m
                                        Mul [Num i, v] ->
                                            Map.alter (\v -> case v of
                                                               Just c -> Just (c + i)
                                                               Nothing -> Just i)
                                                                    v
                                                                    m
                                        _ -> Map.alter (\v -> case v of
                                                                Just c -> Just (c + 1)
                                                                Nothing -> Just 1)
                                                                     e
                                                                     m)
                                             (Map.empty :: Map Expr Integer)
                                             es_n


        new_es = [Num coeff] ++ map (\(v, i) -> Mul [Num i, v]) (Map.assocs pps_to_count)
    in
      Add new_es

normalize_mul :: [Expr] -> Bool -> Expr
normalize_mul es norm =
    let es_n = if norm then map normalize es else es
        coeff = foldl (\n e -> case e of
                                 Num i -> n * i
                                 Mul [Num i, v] -> n * i
                                 _ -> n) 1 es_n
    in
      if coeff == 0 then Num 0 else
          let new_multiplicands = concatMap (\e -> case e of
                                                     Mul [Num i, v] -> [v]
                                                     Num i -> []
                                                     _ -> [e]) es_n
              has_add = any (== True) (map (\e -> case e of
                                                    Add _ -> True
                                                    _ -> False) es_n)
          in
            if null new_multiplicands then Num coeff else
                Mul ((Num coeff):new_multiplicands)
--                Mul ((Num coeff):new_multiplicands)
-- TODO(dhs): not going to SOM
