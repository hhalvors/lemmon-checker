-- src/TruthTable.hs
{-# LANGUAGE TupleSections #-}
module TruthTable
  ( truthTable          -- :: PredFormula -> Either String [(Map String Bool, Bool)]
  , propsIn
  , isPropTaut
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
    go (Iff φ ψ)      = go φ `S.union` go ψ
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
    go (Iff φ ψ)      = go φ `S.union` go ψ
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

-- Treat as atomic for propositional purposes:
--   * Predicate p args
--   * ForAll x φ
--   * Exists x φ
-- Booleans are genuine truth constants, not variables.
atomsIn :: PredFormula -> S.Set PredFormula
atomsIn = go
  where
    go f@(Predicate _ _) = S.singleton f
    go f@(ForAll _ _)    = S.singleton f
    go f@(Exists _ _)    = S.singleton f
    go (Boolean _)       = S.empty
    go (Not φ)           = go φ
    go (And φ ψ)         = go φ `S.union` go ψ
    go (Or  φ ψ)         = go φ `S.union` go ψ
    go (Implies φ ψ)     = go φ `S.union` go ψ
    go (Iff φ ψ)         = go φ `S.union` go ψ

-- A generic version of your allAssignments,
-- but over arbitrary key type (e.g. PredFormula).
allAssignmentsAtoms :: (Ord a) => [a] -> [Map a Bool]
allAssignmentsAtoms names =
  let step name acc = [ M.insert name b m | b <- [False, True], m <- acc ]
  in foldr step [M.empty] names

-- Pure propositional evaluation: Boolean is a truth constant;
-- other atoms are looked up in the valuation.
evalProp :: Map PredFormula Bool -> PredFormula -> Bool
evalProp env (Boolean b)       = b
evalProp env (Not φ)           = not (evalProp env φ)
evalProp env (And φ ψ)         = evalProp env φ && evalProp env ψ
evalProp env (Or  φ ψ)         = evalProp env φ || evalProp env ψ
evalProp env (Implies φ ψ)     = (not (evalProp env φ)) || evalProp env ψ
evalProp env (Iff φ ψ)         = evalProp env φ == evalProp env ψ   -- NEW

-- For everything that we are treating as atomic in the propositional view:
evalProp env a@(Predicate _ _) = lookupAtom env a
evalProp env a@(ForAll _ _)    = lookupAtom env a
evalProp env a@(Exists _ _)    = lookupAtom env a

-- Top-level helper: avoids any layout / where-scope issues
lookupAtom :: Map PredFormula Bool -> PredFormula -> Bool
lookupAtom env f =
  case M.lookup f env of
    Just b  -> b
    Nothing ->
      error ("evalProp: missing value for atomic formula: " ++ show f)

-- Check: Γ propositionally entails Δ, treating quantified formulas as atoms.
isPropTaut :: [PredFormula] -> PredFormula -> Bool
isPropTaut premises conclusion =
  let combined :: PredFormula
      combined =
        case premises of
          [] -> conclusion
          _  -> foldr1 And premises `Implies` conclusion

      atoms      = S.toList (atomsIn combined)
      valuations =
        if null atoms then [M.empty] else allAssignmentsAtoms atoms
  in all (\env -> evalProp env combined) valuations
