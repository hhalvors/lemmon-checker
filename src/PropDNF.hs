-- src/PropDNF.hs
module PropDNF
  ( Lit
  , toDNF          -- ^ Convert a propositional formula to DNF (Either with error)
  , toNNF          -- ^ Eliminate → and push ¬ inward (propositional)
  , clauses        -- ^ NNF -> list of clauses (each clause = list of literals)
  ) where

import ProofTypes

-- A propositional literal: (predicate name, polarity)
-- True  = positive literal  (P)
-- False = negated literal   (¬P)
type Lit = (String, Bool)

--------------------------------------------------------------------------------
-- Public: DNF pipeline
--------------------------------------------------------------------------------

-- | Convert a propositional formula to DNF.
--   Fails if there are quantifiers or any non-0-ary predicate occurs.
toDNF :: PredFormula -> Either String PredFormula
toDNF φ = do
  ensurePropositional φ
  let ψ = toNNF φ
  cs <- clauses ψ
  pure (mkOr (map clauseToFormula cs))
  where
    clauseToFormula :: [Lit] -> PredFormula
    clauseToFormula lits = mkAnd (map litToFormula lits)

    litToFormula :: Lit -> PredFormula
    litToFormula (p, True)  = Predicate p []
    litToFormula (p, False) = Not (Predicate p [])

    mkAnd :: [PredFormula] -> PredFormula
    mkAnd []     = Boolean True
    mkAnd (x:xs) = foldl And x xs

    mkOr :: [PredFormula] -> PredFormula
    mkOr []     = Boolean False
    mkOr (x:xs) = foldl Or x xs

-- | Eliminate → and push ¬ inward (De Morgan), staying within propositional
--   syntax (no quantifiers, no n-ary predicates).
toNNF :: PredFormula -> PredFormula
toNNF = nnf . elimImplies

--------------------------------------------------------------------------------
-- Step 1: reject non-propositional input
--------------------------------------------------------------------------------

-- | Ensure: no quantifiers; every predicate is 0-ary.
ensurePropositional :: PredFormula -> Either String ()
ensurePropositional (Predicate p ts) =
  case ts of
    [] -> Right ()
    _  -> Left $ "Non-propositional predicate: " ++ p ++ "/" ++ show (length ts)
ensurePropositional (Boolean _)      = Right ()
ensurePropositional (Not φ)          = ensurePropositional φ
ensurePropositional (And φ ψ)        = ensurePropositional φ >> ensurePropositional ψ
ensurePropositional (Or  φ ψ)        = ensurePropositional φ >> ensurePropositional ψ
ensurePropositional (Implies φ ψ)    = ensurePropositional φ >> ensurePropositional ψ
ensurePropositional (ForAll _ _)     = Left "Quantifiers are not allowed in propositional DNF."
ensurePropositional (Exists _ _)     = Left "Quantifiers are not allowed in propositional DNF."

--------------------------------------------------------------------------------
-- Step 2: eliminate implication, then push negations inward
--------------------------------------------------------------------------------

elimImplies :: PredFormula -> PredFormula
elimImplies (Implies φ ψ) = Or (Not (elimImplies φ)) (elimImplies ψ)
elimImplies (And φ ψ)     = And (elimImplies φ) (elimImplies ψ)
elimImplies (Or  φ ψ)     = Or  (elimImplies φ) (elimImplies ψ)
elimImplies (Not φ)       = Not (elimImplies φ)
elimImplies x             = x  -- Predicate, Boolean, ForAll/Exists shouldn't appear (rejected earlier)

nnf :: PredFormula -> PredFormula
nnf (Not (Not φ))       = nnf φ
nnf (Not (And φ ψ))     = Or  (nnf (Not φ)) (nnf (Not ψ))
nnf (Not (Or  φ ψ))     = And (nnf (Not φ)) (nnf (Not ψ))
nnf (Not (Boolean b))   = Boolean (not b)
nnf (Not p@(Predicate _ _)) = Not p  -- keep negation only on literals
nnf (And φ ψ)           = And (nnf φ) (nnf ψ)
nnf (Or  φ ψ)           = Or  (nnf φ) (nnf ψ)
nnf x                   = x  -- Predicate, Boolean

--------------------------------------------------------------------------------
-- Step 3: NNF -> list of clauses
--------------------------------------------------------------------------------

-- | Extract a literal from an NNF node.
litOf :: PredFormula -> Either String Lit
litOf (Predicate p [])        = Right (p, True)
litOf (Not (Predicate p []))  = Right (p, False)
litOf _                       = Left "Expected a propositional literal in NNF."

-- | Convert an NNF formula to a disjunction of conjunctions:
--   returns a list of clauses; each clause is a list of literals.
--   Identities:
--     ⊤ -> [[]]   (one empty clause; neutral for ∧-combination)
--     ⊥ -> []     (no clauses; neutral for ∨-combination)
clauses :: PredFormula -> Either String [[Lit]]
clauses (Boolean True)  = Right [[]]
clauses (Boolean False) = Right []
clauses (Or  φ ψ)       = (++) <$> clauses φ <*> clauses ψ
clauses (And φ ψ)       = do
  a <- clauses φ
  b <- clauses ψ
  pure [ ca ++ cb | ca <- a, cb <- b ]
clauses lit             = do
  l <- litOf lit
  pure [[l]]
