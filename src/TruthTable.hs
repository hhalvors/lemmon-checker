-- src/TruthTable.hs
{-# LANGUAGE TupleSections #-}

module TruthTable
  ( truthTable
  , propsIn
  , isPropTaut
  , TruthTableData(..)
  , TTToken(..)
  , Tok(..)
  , TTRow(..)
  , buildTruthTableData
  ) where

import           ProofTypes
import           ModelSemantics                  (Model(..), evalClosed)
import qualified Data.Set            as S
import qualified Data.Map.Strict     as M
import           Data.Map.Strict     (Map)
import qualified Data.List as L
import LatexPretty (isBinary)

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

--------------------------------------------------------------------------------
-- Full token/value matrix truth table (Rieppel-style)
--------------------------------------------------------------------------------

data Tok
  = TLParen
  | TRParen
  | TNot
  | TAnd
  | TOr
  | TImpl
  | TIff
  | TAtom String
  | TConst Bool
  deriving (Eq, Ord, Show)

-- A token column, optionally annotated with the subformula whose truth-value
-- belongs in that column (Nothing for parentheses).
data TTToken = TTToken
  { tokSym   :: Tok
  , tokForm  :: Maybe PredFormula
  } deriving (Eq, Show)

data TTRow = TTRow
  { rowValuation :: Map String Bool
  , rowTokVals   :: [Maybe Bool]      -- aligned with ttTokens
  } deriving (Eq, Show)

data TruthTableData = TruthTableData
  { ttProps   :: [String]   -- valuation columns, sorted
  , ttTokens  :: [TTToken]  -- formula token columns
  , ttMainIx  :: Int        -- index of main connective token column
  , ttRows    :: [TTRow]
  } deriving (Eq, Show)

-- Build the entire token/value matrix.
-- Requires propositional-only (0-ary predicates only), same as truthTable.
buildTruthTableData :: PredFormula -> Either String TruthTableData
buildTruthTableData φ =
  let offenders = S.toList (offendingPreds φ)
  in if not (null offenders)
        then Left $ "Non-propositional symbols present (arity > 0): " ++ show offenders
        else
          let props  = L.sort (S.toList (propsIn φ))
              vals   = allAssignments props
              toks   = tokensTop φ
              mainIx = case L.findIndex (\tt -> tokForm tt == Just φ) toks of
                         Just i  -> i
                         Nothing -> 0  -- should not happen; safe fallback
          in do
            rows <- traverse (mkRow toks) vals
            pure $ TruthTableData props toks mainIx rows
  where
    mkRow :: [TTToken] -> Map String Bool -> Either String TTRow
    mkRow toks valMap = do
      let m = modelFromValuation valMap
      vs <- traverse (evalTok m) toks
      pure $ TTRow valMap vs

    evalTok :: Model -> TTToken -> Either String (Maybe Bool)
    evalTok _ (TTToken _ Nothing)   = Right Nothing
    evalTok m (TTToken _ (Just ψ))  = Just <$> evalClosed m ψ

--------------------------------------------------------------------------------
-- Tokenization (no outermost parentheses; Not binds tightly unless over binary)
--------------------------------------------------------------------------------

tokensTop :: PredFormula -> [TTToken]
tokensTop = stripOuterParens . tok False
  where
    -- tok needParens φ: if needParens=True and φ is binary, wrap in ( ... )
    tok :: Bool -> PredFormula -> [TTToken]
    tok needParens f@(And φ ψ)     = bin needParens TAnd  f φ ψ
    tok needParens f@(Or  φ ψ)     = bin needParens TOr   f φ ψ
    tok needParens f@(Implies φ ψ) = bin needParens TImpl f φ ψ
    tok needParens f@(Iff φ ψ)     = bin needParens TIff  f φ ψ

    tok _ (Boolean b) = [TTToken (TConst b) (Just (Boolean b))]

    tok _ p@(Predicate name args)
      | null args  = [TTToken (TAtom name) (Just p)]
      | otherwise  = [TTToken (TAtom name) (Just p)]  -- should not occur here

    tok needParens f@(Not φ) =
      let headTok = [TTToken TNot (Just f)]
          argNeedsParens = isBinary φ
          argToks = tok argNeedsParens φ
          body = headTok ++ (if argNeedsParens then [TTToken TLParen Nothing] ++ argToks ++ [TTToken TRParen Nothing]
                                            else argToks)
      in if needParens && isBinary f
            then [TTToken TLParen Nothing] ++ body ++ [TTToken TRParen Nothing]
            else body

    -- Quantifiers shouldn't occur in prop-table mode, but keep them tokenizable
    tok _ q@(ForAll _ _) = [TTToken (TAtom (show q)) (Just q)]
    tok _ q@(Exists _ _) = [TTToken (TAtom (show q)) (Just q)]

    bin :: Bool -> Tok -> PredFormula -> PredFormula -> PredFormula -> [TTToken]
    bin needParens opTok whole l r =
      let left  = tok True l
          mid   = [TTToken opTok (Just whole)]   -- value lives under connective
          right = tok True r
          core  = left ++ mid ++ right
      in if needParens
            then [TTToken TLParen Nothing] ++ core ++ [TTToken TRParen Nothing]
            else core

stripOuterParens :: [TTToken] -> [TTToken]
stripOuterParens toks =
  case toks of
    (TTToken TLParen Nothing : rest)
      | not (null rest)
      , last rest == TTToken TRParen Nothing
      , firstParenClosesAtEnd toks
      -> init rest
    _ -> toks

-- True iff the paren opened at the very first token closes at the very last token.
firstParenClosesAtEnd :: [TTToken] -> Bool
firstParenClosesAtEnd xs = go 0 xs
  where
    go :: Int -> [TTToken] -> Bool
    go _ [] = False
    go k [TTToken TRParen Nothing]
      = k == 1
    go k (TTToken TLParen Nothing : ys) = go (k+1) ys
    go k (TTToken TRParen Nothing : ys)
      | k == 1    = False   -- closed *before* the end → not outermost
      | otherwise = go (k-1) ys
    go k (_ : ys) = go k ys                 

