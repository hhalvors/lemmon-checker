-- src/PipeParse.hs
{-# LANGUAGE OverloadedStrings #-}

module PipeParse
  ( parsePipeProof        -- <- export this
  , parsePipeLine         -- (optional) if you want it elsewhere
  ) where

import           ProofTypes
import           FormulaParser               (parseFormula)

import qualified Data.Set                   as S
import           Data.Char                   (isDigit, isSpace, toUpper)
import           Data.List.Split             (splitOneOf, splitOn)

--------------------------------------------------------------------------------
-- Small helpers
--------------------------------------------------------------------------------

trim :: String -> String
trim = f . f where f = reverse . dropWhile isSpace

splitPipes :: String -> [String]
splitPipes = map trim . splitOneOf "|"

readInt :: String -> Maybe Int
readInt s | not (null s) && all isDigit s = Just (read s)
          | otherwise                     = Nothing

parseRefs :: String -> S.Set Int
parseRefs raw =
  let toks = filter (not . null) $ map trim $ splitOneOf " ,\t" raw
  in S.fromList [ n | t <- toks, Just n <- [readInt t] ]

-- Parse a comma-separated list of integers (no rule text here).
readInts :: String -> Either String [Int]
readInts s =
  let parts  = splitOn "," (filter (not . isSpace) s)
      parsed = map (\t -> case reads t of [(n,"")] -> Right n; _ -> Left t) parts
  in case sequence parsed of
       Right xs -> Right xs
       Left bad -> Left $ "Expected integer list before rule, got: " ++ show bad

--------------------------------------------------------------------------------
-- Justification parsing (strict: numbers first, then rule; ∀I var optional)
--------------------------------------------------------------------------------

normalizeRule :: String -> String
normalizeRule raw =
  let u = map toUpper raw
  in case u of
       -- Assumption
       "A"           -> "A"
       "ASSUMPTION"  -> "A"

       -- Propositional rules
       "MP"          -> "MP"
       "MT"          -> "MT"
       "DN"          -> "DN"
       "CP"          -> "CP"
       "ANDI"        -> "∧I"
       "ANDE"        -> "∧E"
       "ORI"         -> "∨I"
       "ORE"         -> "∨E"

       -- Quantifier rules
       "FORALLE"     -> "∀E"
       "UE"          -> "∀E"  -- short form
       "FORALLI"     -> "∀I"
       "UI"          -> "∀I"  -- short form
       "EXISTSI"     -> "∃I"
       "EI"          -> "∃I"  -- short form
       "EXISTSE"     -> "∃E"
       "EE"          -> "∃E"  -- short form

       other         -> other


-- NOTE: we inspect the *target* formula to infer the ∀I variable when omitted.
parseJustification :: PredFormula -> String -> Either String Justification
parseJustification phi raw0 =
  let raw   = trim raw0
      ws    = words raw
  in case ws of
       ["A"] -> Right Assumption

       -- "<nums> <RULE>"
       [numsTxt, ruleTxt] -> do
         ns <- readInts numsTxt
         case normalizeRule ruleTxt of
           "A"  -> if null ns then Right Assumption
                               else Left "Assumption takes no line numbers"
           "MP" -> case ns of [m,n] -> Right (MP m n); _ -> Left "MP needs two refs"
           "MT" -> case ns of [m,n] -> Right (MT m n); _ -> Left "MT needs two refs"
           "DN" -> case ns of [m]   -> Right (DN m);     _ -> Left "DN needs one ref"
           "CP" -> case ns of [m,n] -> Right (CP m n);   _ -> Left "CP needs two refs"
           "∧I" -> case ns of [m,n] -> Right (AndIntro m n); _ -> Left "∧I needs two refs"
           "∧E" -> case ns of [m]   -> Right (AndElim m);    _ -> Left "∧E needs one ref"
           "∨I" -> case ns of [m]   -> Right (OrIntro m);    _ -> Left "∨I needs one ref"
           "∨E" -> case ns of [d,a1,p,a2,c] -> Right (OrElim d a1 p a2 c)
                              _              -> Left "∨E needs five refs (d,a1,p,a2,c)"
           "∀E" -> case ns of [m]   -> Right (ForallElim m); _ -> Left "∀E needs one ref"
           "∃I" -> case ns of [m]   -> Right (ExistsIntro m); _ -> Left "∃I needs one ref"
           "∃E" -> case ns of [m,a,n] -> Right (ExistsElim m a n)
                              _         -> Left "∃E needs three refs (m,a,n)"
           "∀I" -> case ns of
                     [m] -> case phi of
                              ForAll x _ -> Right (ForallIntro m x)  -- infer x from goal
                              _          -> Left "∀I: target line must be ∀x φ to infer x"
                     _   -> Left "∀I needs exactly one ref"
           other -> Left $ "Unknown rule: " ++ other

       -- "<m> ∀I x" (explicit variable still accepted)
       [numsTxt, ruleTxt, varTxt] -> do
         ns <- readInts numsTxt
         case normalizeRule ruleTxt of
           "∀I" -> case ns of [m] -> Right (ForallIntro m varTxt)
                              _    -> Left "∀I needs exactly one ref (m) and a variable x"
           other -> Left $ "Unexpected trailing token for rule " ++ other

       _ -> Left $ "Bad justification format (need \"<nums> <RULE>\" or \"<m> ∀I x\"): " ++ raw

-- One pipe line → ProofLine
parsePipeLine :: String -> Either String ProofLine
parsePipeLine rawLine = do
  let cols = splitPipes rawLine
  case cols of
    [depsC, lineC, formulaC, justC] -> do
      ln <- maybe (Left $ "Bad line number: " ++ show lineC) Right (readInt lineC)
      φ  <- either (Left . ("Formula parse error: "++)) Right (parseFormula formulaC)
      j  <- parseJustification φ justC
      let refs = parseRefs depsC
      pure $ ProofLine ln φ j refs
    _ -> Left $ "Expected 4 columns separated by '|', got: " ++ show cols

-- Whole text (with optional leading "PROOF" header) → Proof
parsePipe :: String -> Either String Proof
parsePipe input =
  let ls0 = filter (not . null) . map trim . lines $ input
      ls  = case ls0 of
              (h:rest) | map toUpper h == "PROOF" -> rest
              _                                   -> ls0
  in traverse parsePipeLine ls

-- public alias expected by Web.hs
parsePipeProof :: String -> Either String Proof
parsePipeProof = parsePipe
