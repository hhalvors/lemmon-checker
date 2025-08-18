-- app/PipeCheck.hs
{-# LANGUAGE OverloadedStrings #-}

module Main where

import           ProofTypes
import           FormulaParser               (parseFormula)
import           PrettyPrint                 (renderFormula)
import           LemmonChecker               (checkProof, proofValid, LineReport(..))

import           Data.Aeson                  (Value(..), (.=), object, encode)
import qualified Data.ByteString.Lazy.Char8 as BL
import qualified Data.Set                   as S

import           Data.Char                   (isDigit, isSpace, toUpper)
import           Data.List.Split             (splitOneOf, splitOn)
import           System.Environment          (getArgs)
import           System.Exit                 (die)

--------------------------------------------------------------------------------
-- Small helpers (duplicated from PipeToJson to keep this exe self-contained)
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
-- Justification parsing (strict: numbers first, then rule, optional var for ∀I)
--------------------------------------------------------------------------------

normalizeRule :: String -> String
normalizeRule raw =
  let u = map toUpper raw
  in case u of
       "A"           -> "A"
       "ASSUMPTION"  -> "A"
       "MP"          -> "MP"
       "MT"          -> "MT"
       "DN"          -> "DN"
       "CP"          -> "CP"
       "ANDI"        -> "∧I"
       "ANDE"        -> "∧E"
       "ORI"         -> "∨I"
       "ORE"         -> "∨E"
       "FORALLE"     -> "∀E"
       "UE"          -> "∀E"
       "FORALLI"     -> "∀I"
       "UI"          -> "∀I"
       "EXISTSI"     -> "∃I"
       "EI"          -> "∃I"
       "EXISTSE"     -> "∃E"
       other         -> other   -- allow already-unicode: ∧I, ∧E, ∨I, ∨E, ∀E, ∀I, ∃I, ∃E

-- NOTE: we infer the variable for ∀I from the target line if not provided
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
                              ForAll x _ -> Right (ForallIntro m x)
                              _          -> Left "∀I: target line must be ∀x φ to infer x"
                     _   -> Left "∀I needs exactly one ref"
           other -> Left $ "Unknown rule: " ++ other

       -- "<m> ∀I x" (still allowed)
       [numsTxt, ruleTxt, varTxt] -> do
         ns <- readInts numsTxt
         case normalizeRule ruleTxt of
           "∀I" -> case ns of [m] -> Right (ForallIntro m varTxt)
                              _    -> Left "∀I needs exactly one ref (m) and a variable x"
           other -> Left $ "Unexpected trailing token for rule " ++ other

       _ -> Left $ "Bad justification format (need \"<nums> <RULE>\" or \"<m> ∀I x\"): " ++ raw

--------------------------------------------------------------------------------
-- Pipe line parsing
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- JSON helpers
--------------------------------------------------------------------------------

lineReportJSON :: LineReport -> Value
lineReportJSON (LineReport _ l note) =
  object
    [ "line"           .= lineNumber l
    , "deps"           .= S.toList (references l)
    , "formulaPretty"  .= renderFormula (formula l)
    , "justification"  .= show (justification l)
    , "ok"             .= either (const False) (const True) note
    , "message"        .= either id (const "") note
    ]

proofJSON :: [LineReport] -> Value
proofJSON reps =
  object
    [ "valid"  .= proofValid reps
    , "lines"  .= map lineReportJSON reps
    ]

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  args <- getArgs
  input <- case args of
    []      -> getContents
    (fp:_)  -> readFile fp

  let ls0 = filter (not . null) . map trim . lines $ input
      ls  = dropWhile (\s -> map toUpper s == "PROOF") ls0

  case traverse parsePipeLine ls of
    Left err -> BL.putStrLn $ encode $ object
      [ "status"  .= String "parse_error"
      , "error"   .= err
      , "raw"     .= input
      ]
    Right proof -> do
      let reps = checkProof proof
      BL.putStrLn $ encode $ object
        [ "status" .= String "ok"
        , "report" .= proofJSON reps
        ]
