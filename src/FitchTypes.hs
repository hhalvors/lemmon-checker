-- FitchTypes.hs
--
-- A Fitch-style presentation of the same proofs the Lemmon checker handles.
--
-- The two notations record the same thing — what a line depends on — but they
-- record it differently, and the difference is the whole subject:
--
--   * Lemmon writes the dependency set out beside every line, and it is
--     *exact*: the set of assumptions actually used.
--
--   * Fitch leaves it implicit in the nesting. A line's dependencies are
--     bounded by the assumptions of the boxes enclosing it — an *upper*
--     bound, not the exact set. A line may well sit inside a box whose
--     assumption it never uses.
--
-- Everything awkward about translating between them follows from that
-- asymmetry, so it is worth stating up front rather than discovering twice.
--
-- Two deliberate choices about which Fitch system this is:
--
--   * Universal introduction takes a side condition rather than a box. Some
--     Fitch systems (Barwise and Etchemendy's among them) open a subproof
--     with a flagged constant and no assumption. Others (forall x: Calgary,
--     for instance) infer ∀xφ(x) from φ(c) provided c occurs in no
--     undischarged assumption. The latter is exactly the condition How Logic
--     Works already imposes, so choosing it makes ∀I translate one line to
--     one line instead of requiring the derivation of φ(c) to be moved
--     bodily into a box.
--
--   * Subproofs are cited by their first and last line, written "3-7", which
--     is the usual Fitch convention and matches how the Lemmon rules here
--     already cite an assumption line together with a conclusion line.
--
-- Line numbers are shared between the two notations: item n in a Fitch proof
-- is line n of the corresponding Lemmon proof. That is what makes the round
-- trip checkable by eye as well as by machine.

module FitchTypes
  ( SubRef
  , FitchRule(..)
  , FitchItem(..)
  , Subproof(..)
  , FitchProof
  , subConclusion
  , subLastLine
  , itemFirstLine
  , itemLastLine
  , fitchLineNumbers
  , renderFitch
  , renderRule
  ) where

import ProofTypes (PredFormula)
import PrettyPrint (renderFormula)
import Data.List (intercalate)

-- | A subproof, cited by the line it assumes and the line it ends on.
type SubRef = (Int, Int)

-- | The rules, one for each rule of How Logic Works.
--
-- Where a Lemmon rule cites an assumption line and a conclusion line — CP,
-- RAA, ∨E, ∃E — the Fitch rule cites a subproof instead. Everything else
-- cites plain line numbers and is unchanged.
data FitchRule
  = FPremise                       -- ^ an assumption never discharged
  | FAssume                        -- ^ the assumption opening a subproof
  | FMP Int Int
  | FMT Int Int
  | FDN Int
  | FCP SubRef                     -- ^ →I
  | FAndI Int Int
  | FAndE Int
  | FOrI Int
  | FOrE Int SubRef SubRef         -- ^ ∨E: the disjunction, then two cases
  | FRAA SubRef                    -- ^ ¬I / reductio
  | FForallE Int
  | FForallI Int                   -- ^ side condition on the name, no box
  | FExistsI Int
  | FExistsE Int SubRef            -- ^ ∃E: the existential, then the case
  | FEqI
  | FEqE Int Int
  | FLEM
  | FPropTaut [Int]
  | FIffI Int Int
  | FIffE Int Int
  | FQN Int
  deriving (Show, Eq)

-- | A proof is a sequence of items; an item is a line or a nested subproof.
data FitchItem
  = FLine Int PredFormula FitchRule
  | FSub Subproof
  deriving (Show, Eq)

-- | A subproof: the assumption that opens it, and what follows.
--
-- The body is never empty in a well-formed proof — a subproof with no
-- conclusion can discharge nothing — but the type does not enforce that,
-- because a partially written proof in an editor legitimately has one.
data Subproof = Subproof
  { subAssumeLine :: Int
  , subAssumeForm :: PredFormula
  , subBody       :: [FitchItem]
  } deriving (Show, Eq)

type FitchProof = [FitchItem]

-- | The formula a subproof ends on, which is what a discharge rule concludes
-- from. Nothing when the body is empty or ends with a nested subproof that is
-- itself empty.
subConclusion :: Subproof -> Maybe PredFormula
subConclusion s =
  case reverse (subBody s) of
    []                -> Nothing
    (FLine _ f _ : _) -> Just f
    (FSub s'    : _)  -> subConclusion s'

-- | The last line number in a subproof, which together with the assumption
-- line is how the subproof is cited.
subLastLine :: Subproof -> Int
subLastLine s =
  case reverse (subBody s) of
    []       -> subAssumeLine s
    (i : _)  -> itemLastLine i

itemFirstLine :: FitchItem -> Int
itemFirstLine (FLine n _ _) = n
itemFirstLine (FSub s)      = subAssumeLine s

itemLastLine :: FitchItem -> Int
itemLastLine (FLine n _ _) = n
itemLastLine (FSub s)      = subLastLine s

-- | Every line number in the proof, in order. Used to check that a
-- translation numbered its output consistently.
fitchLineNumbers :: FitchProof -> [Int]
fitchLineNumbers = concatMap go
  where
    go (FLine n _ _) = [n]
    go (FSub s)      = subAssumeLine s : concatMap go (subBody s)

--------------------------------------------------------------------------------
-- Rendering
--------------------------------------------------------------------------------

renderRule :: FitchRule -> String
renderRule r =
  case r of
    FPremise        -> "Premise"
    FAssume         -> "Assume"
    FMP m n         -> "MP " ++ refs [m, n]
    FMT m n         -> "MT " ++ refs [m, n]
    FDN m           -> "DN " ++ refs [m]
    FCP s           -> "CP " ++ sub s
    FAndI m n       -> "\8743I " ++ refs [m, n]
    FAndE m         -> "\8743E " ++ refs [m]
    FOrI m          -> "\8744I " ++ refs [m]
    FOrE d s1 s2    -> "\8744E " ++ intercalate ", " [show d, sub s1, sub s2]
    FRAA s          -> "RAA " ++ sub s
    FForallE m      -> "\8704E " ++ refs [m]
    FForallI m      -> "\8704I " ++ refs [m]
    FExistsI m      -> "\8707I " ++ refs [m]
    FExistsE m s    -> "\8707E " ++ show m ++ ", " ++ sub s
    FEqI            -> "=I"
    FEqE m n        -> "=E " ++ refs [m, n]
    FLEM            -> "LEM"
    FPropTaut ms    -> "TAUT " ++ refs ms
    FIffI m n       -> "\8596I " ++ refs [m, n]
    FIffE m n       -> "\8596E " ++ refs [m, n]
    FQN m           -> "QN " ++ refs [m]
  where
    refs ns      = intercalate "," (map show ns)
    sub (a, c)   = show a ++ "-" ++ show c

-- | Render a proof in the usual Fitch shape: a vertical bar for each open
-- subproof, and a rule under the assumption that opens one.
--
--     1 | P → Q          Premise
--     2 | | P            Assume
--     3 | | Q            MP 1,2
--     4 | P → Q          CP 2-3
renderFitch :: FitchProof -> String
renderFitch = unlines . concatMap (go 0)
  where
    -- The column the rules start in. Fixed, so that rules line up down the
    -- page regardless of how deeply the formula beside them is nested.
    ruleCol = 46

    go :: Int -> FitchItem -> [String]
    go d (FLine n f r) = [row d n (renderFormula f) (renderRule r)]
    go d (FSub s) =
      row (d + 1) (subAssumeLine s) (renderFormula (subAssumeForm s)) "Assume"
      : sep (d + 1)
      : concatMap (go (d + 1)) (subBody s)

    -- Gutter, then one bar per enclosing box, then the formula. The space
    -- after the number belongs to the gutter rather than to the bars, so that
    -- a line at depth 0 and a line at depth 1 agree about where the gutter
    -- ends and indentation begins.
    row d n f rule =
      let pre = padNum n ++ " " ++ bars d
          gap = max 1 (ruleCol - length pre - length f)
      in pre ++ f ++ replicate gap ' ' ++ rule

    -- The rule under a subproof's assumption, drawn at that box's own depth.
    sep d = replicate 5 ' ' ++ bars (d - 1) ++ "\9500" ++ replicate 12 '\9472'

    bars d   = concat (replicate d "\9474 ")
    padNum n = let s = show n in replicate (max 0 (4 - length s)) ' ' ++ s
