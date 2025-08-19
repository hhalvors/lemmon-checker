-- src/TruthTable.hs
{-# LANGUAGE TupleSections #-}
module TruthTable
  ( truthTable          -- :: PredFormula -> Either String [(Map String Bool, Bool)]
  , propsIn
  ) where

import           ProofTypes
import           ModelSemantics                  (Model(..), evalClosed)
import qualified Data.Set            as S
import qualified Data.Map.Strict     as M
import           Data.Map.Strict     (Map)

-- collect 0-ary predicate names
propsIn :: PredFormula -> S.Set String
propsIn = go
  where
    go (Predicate p args) = if null args then S.singleton p else S.empty
    go (Boolean _)        = S.empty
    go (Not φ)            = go φ
    go (And φ ψ)          = go φ `S.union` go ψ
    go (Or  φ ψ)          = go φ `S.union` go ψ
    go (Implies φ ψ)      = go φ `S.union` go ψ
    go (ForAll _ φ)       = go φ
    go (Exists _ φ)       = go φ

-- find any predicates with arity > 0 (reject if any exist)
offendingPreds :: PredFormula -> S.Set (String, Int)
offendingPreds = go
  where
    go (Predicate p args)
      | null args = S.empty
      | otherwise = S.singleton (p, length args)
    go (Boolean _)    = S.empty
    go (Not φ)        = go φ
    go (And φ ψ)      = go φ `S.union` go ψ
    go (Or  φ ψ)      = go φ `S.union` go ψ
    go (Implies φ ψ)  = go φ `S.union` go ψ
    go (ForAll _ φ)   = go φ
    go (Exists _ φ)   = go φ

-- enumerate all Boolean assignments for 0-ary names
allAssignments :: [String] -> [Map String Bool]
allAssignments names =
  let step name acc = [ M.insert name b m | b <- [False, True], m <- acc ]
  in foldr step [M.empty] names

-- 0-ary predicate relation encoding: True ↦ {[]}, False ↦ ∅
zeroAryRel :: Bool -> S.Set [String]
zeroAryRel True  = S.singleton []
zeroAryRel False = S.empty

-- build a Model from a 0-ary valuation (singleton domain for ∀/∃)
modelFromValuation :: Map String Bool -> Model
modelFromValuation val =
  let dom    = S.singleton "d"
      consts = M.empty
      preds  = M.fromList [ ((p,0), zeroAryRel b) | (p,b) <- M.toList val ]
  in Model { domain = dom, constInterp = consts, predInterp = preds }

-- main: error if any arity>0; otherwise evaluate via ModelSemantics
truthTable :: PredFormula -> Either String [(Map String Bool, Bool)]
truthTable φ =
  let offenders = S.toList (offendingPreds φ)
  in if not (null offenders)
        then Left $ "Non-propositional symbols present (arity > 0): "
                 ++ show offenders
        else
          let names = S.toList (propsIn φ)
              vals  = allAssignments names
          in traverse (\m -> fmap (m,) (evalClosed (modelFromValuation m) φ)) vals
