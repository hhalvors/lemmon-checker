-- src/ModelSemantics.hs
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module ModelSemantics
  ( Entity
  , Model(..)
  , VAssign
  , emptyAssign
  , assign
  , interpretConst
  , interpretPred
  , fromTuples
  , eval
  , evalClosed
  , freeVars
  ) where

import           ProofTypes
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import           Data.Set        (Set)
import qualified Data.Set        as S
import           Data.Maybe      (fromMaybe)
import           Control.Monad   (foldM)
import qualified Data.Aeson      as A
import           Data.Aeson      ((.=))  -- we’ll qualify the rest as A..:
import           Data.Char       (isLower)

-- ──────────────────────────────────────────────────────────────────────────────
-- Core types
-- ──────────────────────────────────────────────────────────────────────────────

type Entity = String
type PredKey = (String, Int)
type VAssign = Map String Entity

emptyAssign :: VAssign
emptyAssign = M.empty

assign :: String -> Entity -> VAssign -> VAssign
assign = M.insert

-- All predicates (including arity 0 for propositional constants) live here.
data Model = Model
  { domain      :: Set Entity
  , constInterp :: Map String Entity
  , predInterp  :: Map PredKey (Set [Entity])  -- 0-ary: [] ∈ rel means True
  } deriving (Show, Eq)

-- ──────────────────────────────────────────────────────────────────────────────
-- JSON instances
--d   - We emit only predInterp (arity 0 encodes props).
--   - We also ACCEPT legacy "propInterp" on input and merge it into predInterp.
-- ──────────────────────────────────────────────────────────────────────────────

instance A.ToJSON Model where
  toJSON (Model d c p) =
    A.object
      [ "domain"      .= S.toList d
      , "constInterp" .= c
      , "predInterp"  .=
          [ A.object [ "name"   .= n
                     , "arity"  .= k
                     , "tuples" .= S.toList rel
                     ]
          | ((n,k), rel) <- M.toList p
          ]
      ]

instance A.FromJSON Model where
  parseJSON = A.withObject "Model" $ \o -> do
    d       <- S.fromList <$> (o A..:  "domain")
    c       <-                (o A..:  "constInterp")
    ps      <-                (o A..:  "predInterp")
    propsMb <-                (o A..:? "propInterp" A..!= (M.empty :: Map String Bool))
    pPairs  <- mapM parsePred ps
    let pRel = M.fromList pPairs
        propPairs =
          [ ((name, 0), if b then S.singleton [] else S.empty)
          | (name, b) <- M.toList propsMb
          ]
        pAll = M.union pRel (M.fromList propPairs)
    pure (Model d c pAll)
    where
      parsePred = A.withObject "PredRelation" $ \p -> do
        n   <- p A..: "name"
        k   <- p A..: "arity"
        tup <- S.fromList <$> (p A..: "tuples")
        pure ((n, k), tup)

-- ──────────────────────────────────────────────────────────────────────────────
-- Helpers to build interpretations
-- ──────────────────────────────────────────────────────────────────────────────

interpretConst :: Model -> String -> Either String Entity
interpretConst m c =
  case M.lookup c (constInterp m) of
    Just v  -> Right v
    Nothing -> Left $ "Uninterpreted constant: " ++ show c

-- STRICT lookup: error if the predicate symbol/arity is absent
interpretPred :: Model -> String -> Int -> Either String (Set [Entity])
interpretPred m p k =
  case M.lookup (p,k) (predInterp m) of
    Just rel -> Right rel
    Nothing  -> Left $ "Uninterpreted predicate: " ++ p ++ "/" ++ show k

fromTuples :: [[Entity]] -> Set [Entity]
fromTuples = S.fromList

-- ──────────────────────────────────────────────────────────────────────────────
-- Term evaluation
-- ──────────────────────────────────────────────────────────────────────────────

evalTerm :: Model -> VAssign -> Term -> Either String Entity
evalTerm _ asg (Var x) =
  case M.lookup x asg of
    Just v  -> Right v
    Nothing -> Left $ "Unbound variable: " ++ show x
evalTerm m _   (Const c) = interpretConst m c

-- ──────────────────────────────────────────────────────────────────────────────
-- Formula evaluation
-- ──────────────────────────────────────────────────────────────────────────────

eval :: Model -> VAssign -> PredFormula -> Either String Bool
eval _ _   (Boolean b)         = Right b

-- Predicates: for arity 0, we check [] ∈ relation (true) / ∉ (false)
eval m asg (Predicate name ts) = do
  vs  <- mapM (evalTerm m asg) ts
  rel <- interpretPred m name (length ts)  -- strict lookup
  pure (vs `S.member` rel)

eval m asg (Not φ)        = not <$> eval m asg φ
eval m asg (And φ ψ)      = (&&) <$> eval m asg φ <*> eval m asg ψ
eval m asg (Or  φ ψ)      = (||) <$> eval m asg φ <*> eval m asg ψ
eval m asg (Implies φ ψ)  = impl <$> eval m asg φ <*> eval m asg ψ
  where impl a b = (not a) || b

eval m asg (ForAll x φ) = do
  let d = S.toList (domain m)
  if null d
     then Left "Empty domain: ∀ has no witnesses."
     else allM (\v -> eval m (assign x v asg) φ) d

eval m asg (Exists x φ) = do
  let d = S.toList (domain m)
  if null d
     then Left "Empty domain: ∃ has no witnesses."
     else anyM (\v -> eval m (assign x v asg) φ) d

-- Closed sentences only (otherwise a helpful error)
evalClosed :: Model -> PredFormula -> Either String Bool
evalClosed m φ =
  if S.null (freeVars φ)
    then eval m emptyAssign φ
    else Left $ "Formula is not closed; free variables: " ++ show (S.toList (freeVars φ))

-- ──────────────────────────────────────────────────────────────────────────────
-- Small Either helpers
-- ──────────────────────────────────────────────────────────────────────────────

allM :: (a -> Either String Bool) -> [a] -> Either String Bool
allM p = foldM (\acc x -> if acc then p x else pure False) True

anyM :: (a -> Either String Bool) -> [a] -> Either String Bool
anyM p = foldM (\acc x -> if acc then pure True else p x) False
