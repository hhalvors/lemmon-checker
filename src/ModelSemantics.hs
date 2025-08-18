{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}

module ModelSemantics
  ( Entity
  , Model(..)
  , VAssign
  , emptyAssign
  , assign
  , interpretConst
  , interpretPred
  , interpretProp
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

-- JSON
import qualified Data.Aeson      as A
import           Data.Aeson      ((.=), (.:))

-- ──────────────────────────────────────────────────────────────────────────────
-- Core types
-- ──────────────────────────────────────────────────────────────────────────────

type Entity = String
type PredKey = (String, Int)     -- (predicate name, arity)
type VAssign = Map String Entity

emptyAssign :: VAssign
emptyAssign = M.empty

assign :: String -> Entity -> VAssign -> VAssign
assign = M.insert

data Model = Model
  { domain      :: Set Entity
  , constInterp :: Map String Entity
  , predInterp  :: Map PredKey (Set [Entity])  -- relations, including unary F,G
  , propInterp  :: Map String Bool             -- 0-ary predicates (propositional constants), e.g., P
  } deriving (Show, Eq)

-- ──────────────────────────────────────────────────────────────────────────────
-- Aeson instances for convenient JSON IO (used by /model/check)
-- ──────────────────────────────────────────────────────────────────────────────

instance A.ToJSON Model where
  toJSON (Model d c p props) =
    A.object
      [ "domain"      .= S.toList d
      , "constInterp" .= c
      , "predInterp"  .=
          [ A.object
              [ "name"   .= n
              , "arity"  .= k
              , "tuples" .= S.toList rel
              ]
          | ((n, k), rel) <- M.toList p
          ]
      , "propInterp"  .= props
      ]

instance A.FromJSON Model where
  parseJSON = A.withObject "Model" $ \o -> do
    d     <- S.fromList <$> o .: "domain"
    c     <- o .: "constInterp"
    ps    <- o .: "predInterp"
    props <- o .: "propInterp"
    p     <- M.fromList <$> mapM parsePred ps
    pure (Model d c p props)
    where
      parsePred = A.withObject "PredRelation" $ \p -> do
        n   <- p .: "name"
        k   <- p .: "arity"
        tup <- S.fromList <$> p .: "tuples"
        pure ((n, k), tup)

-- ──────────────────────────────────────────────────────────────────────────────
-- Helpers for building interpretations
-- ──────────────────────────────────────────────────────────────────────────────

interpretConst :: Model -> String -> Either String Entity
interpretConst m c =
  case M.lookup c (constInterp m) of
    Just v  -> Right v
    Nothing -> Left $ "Uninterpreted constant: " ++ show c

-- STRICT lookup: error if a predicate is uninterpreted
interpretPred :: Model -> String -> Int -> Either String (Set [Entity])
interpretPred m p k =
  case M.lookup (p,k) (predInterp m) of
    Just rel -> Right rel
    Nothing  -> Left $ "Uninterpreted predicate: " ++ p ++ "/" ++ show k    

interpretProp :: Model -> String -> Maybe Bool
interpretProp m name = M.lookup name (propInterp m)

fromTuples :: [[Entity]] -> Set [Entity]
fromTuples = S.fromList

-- ──────────────────────────────────────────────────────────────────────────────
-- Free variables
-- ──────────────────────────────────────────────────────────────────────────────

freeVars :: PredFormula -> Set String
freeVars = go S.empty
  where
    go bound (Predicate _ ts) = S.fromList [ x | Var x <- ts, x `S.notMember` bound ]
    go _     (Boolean _)      = S.empty
    go b     (Not φ)          = go b φ
    go b     (And φ ψ)        = go b φ `S.union` go b ψ
    go b     (Or  φ ψ)        = go b φ `S.union` go b ψ
    go b     (Implies φ ψ)    = go b φ `S.union` go b ψ
    go b     (ForAll x φ)     = go (S.insert x b) φ
    go b     (Exists x φ)     = go (S.insert x b) φ

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
eval _ _   (Boolean b)           = Right b
eval m asg (Predicate name ts) = do
  vs  <- mapM (evalTerm m asg) ts              -- evaluate each term
  rel <- interpretPred m name (length ts)      -- STRICT lookup (Either)
  pure (vs `S.member` rel)                     -- [] ∈ rel handles 0-ary

eval m asg (Not φ)        = not <$> eval m asg φ
eval m asg (And φ ψ)      = (&&) <$> eval m asg φ <*> eval m asg ψ
eval m asg (Or  φ ψ)      = (||) <$> eval m asg φ <*> eval m asg ψ
eval m asg (Implies φ ψ)  = (impl) <$> eval m asg φ <*> eval m asg ψ
  where impl a b = (not a) || b
eval m asg (ForAll x φ)   = do
  let d = S.toList (domain m)
  if null d
     then Left "Empty domain: ∀ has no witnesses."
     else allM (\v -> eval m (assign x v asg) φ) d
eval m asg (Exists x φ)   = do
  let d = S.toList (domain m)
  if null d
     then Left "Empty domain: ∃ has no witnesses."
     else anyM (\v -> eval m (assign x v asg) φ) d

evalClosed :: Model -> PredFormula -> Either String Bool
evalClosed m φ =
  if S.null (freeVars φ)
    then eval m emptyAssign φ
    else Left $ "Formula is not closed; free variables: " ++ show (S.toList (freeVars φ))

-- small Either helpers
allM :: (a -> Either String Bool) -> [a] -> Either String Bool
allM p = foldM (\acc x -> if acc then p x else pure False) True

anyM :: (a -> Either String Bool) -> [a] -> Either String Bool
anyM p = foldM (\acc x -> if acc then pure True else p x) False

