-- ProofTypes.hs
{-# LANGUAGE DeriveGeneric #-}

module ProofTypes
  ( Term(..)
  , PredFormula(..)
  , Justification(..)
  , ProofLine(..)
  , Proof(..)
  , substFree
  , freeFor
  , freeVars
  , varsInFormula
  , constsInFormula
  , isEq
  , equalUpToConstReplacement
  ) where

import GHC.Generics (Generic)
import Data.Aeson (ToJSON, FromJSON)
import Data.Set (Set)
import qualified Data.Set as S
import Data.List (nub)

-- Term type for predicate logic
data Term
  = Var String
  | Const String
  deriving (Show, Eq, Ord, Generic)

instance FromJSON Term
instance ToJSON Term

-- Formula type
data PredFormula
  = Predicate String [Term]
  | Boolean Bool
  | Not PredFormula
  | And PredFormula PredFormula
  | Or PredFormula PredFormula
  | Implies PredFormula PredFormula
  | Iff PredFormula PredFormula 
  | ForAll String PredFormula
  | Exists String PredFormula
  deriving (Show, Eq, Ord, Generic)

instance FromJSON PredFormula
instance ToJSON PredFormula

-- Justifications
data Justification
  = Assumption
  | MP Int Int
  | MT Int Int
  | DN Int
  | CP Int Int
  | AndIntro Int Int
  | AndElim Int
  | OrIntro Int
  | OrElim Int Int Int Int Int
  | RAA Int Int  -- refers to assumption line and contradiction line
  | ForallElim Int 
  | ExistsIntro Int
  | ForallIntro Int -- introducing ∀x from line Int
  | ExistsElim Int Int Int  -- m = ∃xφ(x), m1 = assumption φ(a), n = result ψ
  | EqIntro
  | EqElim Int Int
  | LEM
  | PropTaut [Int]
   -- NEW:
  | IffIntro Int Int   -- from lines m,n: ϕ→ψ and ψ→ϕ
  | IffElim Int Int    -- from lines m,n: ϕ↔ψ and ϕ (or ψ) to get ψ (or ϕ)
  | QN Int   
  deriving (Show, Eq, Generic)

instance FromJSON Justification
instance ToJSON Justification

-- One line of a proof
data ProofLine = ProofLine
  { lineNumber    :: Int
  , formula       :: PredFormula
  , justification :: Justification
  , references    :: Set Int
  } deriving (Show, Eq, Generic)

instance FromJSON ProofLine
instance ToJSON ProofLine

type Proof = [ProofLine]

varsInTerm :: Term -> Set String
varsInTerm (Var v)   = S.singleton v
varsInTerm (Const _) = S.empty

constsInTerm :: Term -> Set String
constsInTerm (Var _)    = S.empty
constsInTerm (Const c)  = S.singleton c

varsInFormula :: PredFormula -> Set String
varsInFormula = go
  where
    go (Predicate _ ts)   = S.unions (map varsInTerm ts)
    go (Not p)            = go p
    go (And p q)          = go p `S.union` go q
    go (Or  p q)          = go p `S.union` go q
    go (Implies p q)      = go p `S.union` go q
    go (Iff p q)          = go p `S.union` go q          -- NEW
    go (ForAll _ p)       = go p
    go (Exists _ p)       = go p

constsInFormula :: PredFormula -> Set String
constsInFormula = go
  where
    go (Predicate _ ts)   = S.unions (map constsInTerm ts)
    go (Not p)            = go p
    go (And p q)          = go p `S.union` go q
    go (Or  p q)          = go p `S.union` go q
    go (Implies p q)      = go p `S.union` go q
    go (Iff p q)          = go p `S.union` go q          -- NEW
    go (ForAll _ p)       = go p
    go (Exists _ p)       = go p

-- Capture-avoidance side condition (no alpha-renaming here) ----------
-- freeFor x t φ  ≡ every free occurrence of x in φ is NOT under any
-- quantifier binding a variable that appears free in t.
freeFor :: String -> Term -> PredFormula -> Bool
freeFor x t = go S.empty
  where
    vt = varsInTerm t  -- variables that appear in the term t
    go :: Set String -> PredFormula -> Bool
    go bound (Predicate _ ts) =
      all (termOK bound) ts
    go bound (Not p)           = go bound p
    go bound (And p q)         = go bound p && go bound q
    go bound (Or  p q)         = go bound p && go bound q
    go bound (Implies p q)     = go bound p && go bound q
    go bound (Iff p q)         = go bound p && go bound q     -- NEW
    go bound (ForAll y p)      = go (S.insert y bound) p
    go bound (Exists y p)      = go (S.insert y bound) p

    termOK :: Set String -> Term -> Bool
    termOK bound (Var v)
      | v == x    = S.null (vt `S.intersection` bound)  -- no capture allowed
      | otherwise = True
    termOK _     (Const _)     = True

-- Substitution of free occurrences only (no α-renaming) ---------------
substFree :: String -> Term -> PredFormula -> PredFormula
substFree x t = go
  where
    subT (Var v)   | v == x    = t
                   | otherwise = Var v
    subT c@(Const _)           = c

    go (Predicate name ts) = Predicate name (map subT ts)
    go (Not p)             = Not (go p)
    go (And p q)           = And (go p) (go q)
    go (Or  p q)           = Or  (go p) (go q)
    go (Implies p q)       = Implies (go p) (go q)
    go (Iff p q)           = Iff (go p) (go q)          
    go (ForAll y p)
      | y == x             = ForAll y p      -- x is bound here; stop
      | otherwise          = ForAll y (go p)
    go (Exists y p)
      | y == x             = Exists y p
      | otherwise          = Exists y (go p)

-- Collect free variables in a term
freeVarsTerm :: Term -> Set String
freeVarsTerm (Var v)   = S.singleton v
freeVarsTerm (Const _) = S.empty

-- Collect free variables in a formula
freeVars :: PredFormula -> Set String
freeVars (Predicate _ args) = S.unions (map freeVarsTerm args)
freeVars (Not f)            = freeVars f
freeVars (And f g)          = freeVars f `S.union` freeVars g
freeVars (Or f g)           = freeVars f `S.union` freeVars g
freeVars (Implies f g)      = freeVars f `S.union` freeVars g
freeVars (Iff f g)          = freeVars f `S.union` freeVars g   -- NEW
freeVars (ForAll x f)       = S.delete x (freeVars f)
freeVars (Exists x f)       = S.delete x (freeVars f)

isEq :: PredFormula -> Maybe (Term, Term)
isEq (Predicate "=" [t1, t2]) = Just (t1, t2)
isEq _                        = Nothing

equalUpToConstReplacement :: String -> String -> PredFormula -> PredFormula -> Bool
equalUpToConstReplacement a b = goF
  where
    eqConst x y =
      (x == a && y == b) || x == y

    goT (Var x)   (Var y)   = x == y
    goT (Const x) (Const y) = eqConst x y
    goT _         _         = False

    goTs xs ys =
      length xs == length ys &&
      and (zipWith goT xs ys)

    goF (Predicate n1 ts1) (Predicate n2 ts2) = n1 == n2 && goTs ts1 ts2
    goF (Not p)            (Not q)            = goF p q
    goF (And p1 p2)        (And q1 q2)        = goF p1 q1 && goF p2 q2
    goF (Or  p1 p2)        (Or  q1 q2)        = goF p1 q1 && goF p2 q2
    goF (Implies p q)      (Implies r s)      = goF p r && goF q s
    goF (Iff p q)          (Iff r s)          = goF p r && goF q s          -- NEW
    goF (ForAll x p)       (ForAll y q)
      | x == y    = goF p q
      | otherwise = False
    goF (Exists x p)       (Exists y q)
      | x == y    = goF p q
      | otherwise = False
    goF _ _ = False

