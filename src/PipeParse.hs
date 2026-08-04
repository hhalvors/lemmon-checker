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
import           Data.List                   (intercalate)
import           Data.List.Split             (splitOneOf, splitOn)

import Normalize (normalizeFormula)
import Data.Bifunctor (first)

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

-- | Canonical name for a rule token.
--
-- Matching is tried exactly first, then case-insensitively. Handwriting is
-- not careful about case — "cP" and "andI" both turn up in the sample
-- photographs — and the OCR pipeline should not fail on that. The exact pass
-- runs first so that case-carrying aliases such as "vI" for ∨I keep working:
-- upper-casing alone would turn "vI" into "VI" and lose it.
ruleAliases :: [(String, String)]
ruleAliases =
  [ ("A", "A"), ("Assumption", "A")

  , ("MP", "MP"), ("MT", "MT"), ("DN", "DN"), ("CP", "CP"), ("QN", "QN")

  , ("∧I", "∧I"), ("&I", "∧I"), ("ANDI", "∧I"), ("/\\I", "∧I")
  , ("∧E", "∧E"), ("&E", "∧E"), ("ANDE", "∧E"), ("/\\E", "∧E")

  , ("∨I", "∨I"), ("vI", "∨I"), ("\\/I", "∨I"), ("ORI", "∨I")
  , ("∨E", "∨E"), ("vE", "∨E"), ("\\/E", "∨E"), ("ORE", "∨E")

  , ("↔I", "↔I"), ("<->I", "↔I"), ("IFFI", "↔I"), ("BIDI", "↔I")
  , ("↔E", "↔E"), ("<->E", "↔E"), ("IFFE", "↔E"), ("BIDE", "↔E")

  , ("RAA", "RAA"), ("RA", "RAA"), ("¬I", "RAA"), ("~I", "RAA")

  , ("∀E", "∀E"), ("UE", "∀E"), ("ForallE", "∀E")
  , ("∀I", "∀I"), ("UI", "∀I"), ("ForallI", "∀I")
  , ("∃I", "∃I"), ("EI", "∃I"), ("ExistsI", "∃I")
  , ("∃E", "∃E"), ("EE", "∃E"), ("ExistsE", "∃E")

  , ("=E", "=E"), ("=I", "=I")

  , ("LEM", "LEM"), ("prop taut", "prop taut")
  ]

-- The same table keyed by upper-cased alias, for the case-insensitive pass.
ruleAliasesUpper :: [(String, String)]
ruleAliasesUpper = [ (map toUpper a, r) | (a, r) <- ruleAliases ]

normalizeRule :: String -> String
normalizeRule raw =
  case lookup raw ruleAliases of
    Just r  -> r
    Nothing ->
      case lookup (map toUpper raw) ruleAliasesUpper of
        Just r  -> r
        Nothing -> raw

-- | The variables bound by a formula's leading run of universal quantifiers.
-- ∀x∀y φ ↦ ["x","y"]; anything not starting with ∀ ↦ [].
forallPrefixVars :: PredFormula -> [String]
forallPrefixVars (ForAll x body) = x : forallPrefixVars body
forallPrefixVars _               = []

-- | "x", or "x and y", or "x, y and z" — for error messages.
describeVars :: [String] -> String
describeVars vs =
  case map (\v -> "\"" ++ v ++ "\"") vs of
    []     -> ""
    [a]    -> a
    [a,b]  -> a ++ " and " ++ b
    xs     -> intercalate ", " (init xs) ++ " and " ++ last xs

parseJustification :: PredFormula -> String -> Either String Justification
parseJustification phi raw0 =
  let raw   = trim raw0
      ws    = words raw
  in case ws of
       ["A"]   -> Right Assumption
       ["=I"]  -> Right EqIntro
       ["LEM"] -> Right LEM

       -- NEW: propositional tautology rule
       ["prop","taut"] ->
         Right (PropTaut [])

       [numsTxt, "prop", "taut"] -> do
         ns <- readInts numsTxt
         Right (PropTaut ns)

       -- "<nums> <RULE>"
       [numsTxt, ruleTxt] -> do
         ns <- readInts numsTxt
         case normalizeRule ruleTxt of
           "A"  -> if null ns then Right Assumption
                               else Left "Assumption takes no line numbers"
           "MP" -> case ns of [m,n] -> Right (MP m n); _ -> Left "MP needs two refs"
           "MT" -> case ns of [m,n] -> Right (MT m n); _ -> Left "MT needs two refs"
           "DN" -> case ns of [m]   -> Right (DN m);     _ -> Left "DN needs one ref"
                      -- NEW: QN (quantifier negation), one cited line
           "QN" ->
             case ns of
               [m] -> Right (QN m)
               _   -> Left "QN needs one ref"
           "CP" -> case ns of [m,n] -> Right (CP m n);   _ -> Left "CP needs two refs"
           "∧I" -> case ns of [m,n] -> Right (AndIntro m n); _ -> Left "∧I needs two refs"
           "∧E" -> case ns of [m]   -> Right (AndElim m);    _ -> Left "∧E needs one ref"
           "∨I" -> case ns of [m]   -> Right (OrIntro m);    _ -> Left "∨I needs one ref"
           "∨E" -> case ns of [d,a1,p,a2,c] -> Right (OrElim d a1 p a2 c)
                              _              -> Left "∨E needs five refs (d,a1,p,a2,c)"
           -- 🔴 NEW: biconditional intro / elim
           "↔I" -> case ns of
                     [m,n] -> Right (IffIntro m n)
                     _     -> Left "↔I needs two refs (lines with ϕ→ψ and ψ→ϕ)"
           "↔E" -> case ns of
                     [m,n] -> Right (IffElim m n)
                     _     -> Left "↔E needs two refs (line with ϕ↔ψ and line with ϕ or ψ)"                   
           "∀E" -> case ns of [m]   -> Right (ForallElim m); _ -> Left "∀E needs one ref"
           "∃I" -> case ns of [m]   -> Right (ExistsIntro m); _ -> Left "∃I needs one ref"
           "∃E" -> case ns of [m,a,n] -> Right (ExistsElim m a n)
                              _         -> Left "∃E needs three refs (m,a,n)"
           "RAA" -> case ns of [a,c] -> Right (RAA a c)
                               _     -> Left "RAA needs two refs (assumption, contradiction)"
           "¬I"  -> case ns of [a,c] -> Right (RAA a c)
                               _     -> Left "¬I needs two refs (assumption, contradiction)"
           "~I"  -> case ns of [a,c] -> Right (RAA a c)
                               _     -> Left "~I needs two refs (assumption, contradiction)"
           "∀I" -> case ns of
                     [m] -> case phi of
                              ForAll x _ -> Right (ForallIntro m)
                              _          -> Left "∀I: target line must be ∀x φ to infer x"
                     _   -> Left "∀I needs exactly one ref"

           "=I" -> case ns of
                     [] -> Right EqIntro
                     _  -> Left "=I takes no line numbers"

           "=E" -> case ns of
                     [m,n] -> Right (EqElim m n)
                     _     -> Left "=E needs two refs (line with a=b, line with φ(a))"

           other -> Left $ "Unknown rule: " ++ other

       -- "<m> ∀I x" (explicit variable still accepted)
       --
       -- ForallIntro carries only the cited line: the variable being
       -- generalised is recoverable from the goal's ∀-prefix. The variable is
       -- therefore not needed, but when a student does write one we check it
       -- rather than discard it, so that "5 ∀I y" against a goal of ∀x(...)
       -- is reported instead of silently ignored.
       [numsTxt, ruleTxt, varTxt] -> do
         ns <- readInts numsTxt
         case normalizeRule ruleTxt of
           "∀I" ->
             case ns of
               [m] ->
                 case forallPrefixVars phi of
                   [] -> Left "∀I: target line must be ∀x φ to infer x"
                   vs | varTxt `elem` vs -> Right (ForallIntro m)
                      | otherwise ->
                          Left $ "∀I: cited variable \"" ++ varTxt
                              ++ "\" is not bound by the goal, which generalises "
                              ++ describeVars vs
                              ++ ". Either name one of those, or drop the variable."
               _ -> Left "∀I needs exactly one ref (m) and a variable x"
           other -> Left $ "Unexpected trailing token for rule " ++ other

       _ -> Left $ "Bad justification format (need \"<nums> <RULE>\" or \"<m> ∀I x\"): " ++ raw


parsePipeLine :: String -> Either String ProofLine
parsePipeLine rawLine = do
  let cols = splitPipes rawLine
  case cols of
    [depsC, lineC, formulaC, justC] -> do
      ln <- maybe (Left $ "Bad line number: " ++ show lineC) Right (readInt lineC)

      -- ✅ normalize only the formula text
      let formTxt = normalizeFormula (trim formulaC)
      φ  <- first ("Formula parse error: " ++) (parseFormula formTxt)

      -- ❌ do NOT normalize the rule token; parseJustification handles rule aliases
      j  <- parseJustification φ (trim justC)

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
