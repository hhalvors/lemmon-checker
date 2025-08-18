-- ProofTypes.hs
{-# LANGUAGE DeriveGeneric #-}

module ProofTypes where

import GHC.Generics (Generic)
import Data.Aeson (ToJSON, FromJSON)
import Data.Set (Set)

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
  | ForAll String PredFormula
  | Exists String PredFormula
  deriving (Show, Eq, Generic)

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
  | ForallIntro Int String  -- introducing ∀x from line Int
  | ExistsElim Int Int Int  -- m = ∃xφ(x), m1 = assumption φ(a), n = result ψ
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

