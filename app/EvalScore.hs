-- app/EvalScore.hs
--
-- Score a set of predicted proof transcriptions against ground truth.
--
--   eval-score <truth-dir> <pred-dir>
--
-- Both directories hold pipe-format files with matching names; every *.pipe
-- in the truth directory is scored. A prediction that is missing or that
-- fails to parse counts as wholly wrong rather than being skipped, so the
-- denominator is always the full corpus.
--
-- Two numbers are reported, and they answer different questions.
--
--   Cell accuracy diagnoses the recogniser. Each proof line has four cells
--   (dependencies, line number, formula, justification) and each is compared
--   after parsing, so a formula that differs only in surface syntax — "P->Q"
--   against "P→Q" — counts as correct. Breaking the score out by column says
--   where to spend effort: formula errors and justification errors have quite
--   different causes.
--
--   A truth file is not required to parse. A page can carry a malformed
--   justification — "6,7 DN", where DN cites one line — and transcribing that
--   faithfully is the correct behaviour: the parser then rejects it and the
--   student is told what is wrong. So the verdict is three-valued, and when
--   either side fails to parse the cells are compared as text instead of as
--   parsed values.
--
--   Verdict agreement is the number that matters to a student. It asks
--   whether the checker reaches the same conclusion from the transcription as
--   from the truth. A misread that leaves the verdict alone is survivable; one
--   that turns a sound proof into a reported error, or silently blesses a
--   broken one, is the failure this pipeline exists to avoid. Note that truth
--   proofs are not assumed to be valid — the corpus deliberately contains
--   invalid ones — so the expected verdict is whatever the checker says about
--   the truth file itself.

module Main where

import           ProofTypes
import           PipeParse          (parsePipeProof)
import           FormulaParser      (parseFormula)
import           Normalize          (normalizeFormula)
import           LemmonChecker      (checkProof, proofValid)

import qualified Data.Map.Strict   as M
import           Data.List          (sort, isSuffixOf)
import           Control.Monad      (forM, unless)
import           System.Directory   (listDirectory, doesFileExist)
import           System.Environment (getArgs)
import           System.Exit        (die, exitFailure, exitSuccess)
import           System.FilePath    ((</>))
import           Text.Printf        (printf)

--------------------------------------------------------------------------------
-- Per-file result
--------------------------------------------------------------------------------

data Verdict = VValid | VInvalid | VUnparseable deriving Eq

showVerdict :: Verdict -> String
showVerdict VValid        = "valid"
showVerdict VInvalid      = "invalid"
showVerdict VUnparseable  = "unparseable"

-- A side of the comparison: the parse if it succeeded, plus the raw cells
-- keyed by the line-number column, which is all we have when it did not.
data Side = Side
  { sProof :: Maybe Proof
  , sCells :: M.Map String [String]
  }

readSide :: String -> Side
readSide txt =
  Side (either (const Nothing) Just (parsePipeProof txt))
       (M.fromList [ (cols !! 1, cols)
                   | l <- lines txt
                   , let cols = splitOn4 l
                   , length cols == 4 ])

splitOn4 :: String -> [String]
splitOn4 s = case break (== '|') s of
  (a, [])      -> [trim a]
  (a, _:rest)  -> trim a : splitOn4 rest
  where trim = dropWhile (== ' ') . reverse . dropWhile (== ' ') . reverse

verdictOf :: Side -> Verdict
verdictOf sd = case sProof sd of
  Nothing -> VUnparseable
  -- An empty transcription is a failure, not a vacuous theorem. proofValid
  -- folds over the lines, so the empty proof comes back True; counting that
  -- as agreement would let a recogniser that produced nothing at all score as
  -- having got the verdict right.
  Just [] -> VUnparseable
  Just p  -> if proofValid (checkProof p) then VValid else VInvalid

data Outcome
  = Missing              -- ^ no prediction file at all
  | Scored Tally

data Tally = Tally
  { tLines     :: Int          -- ^ truth lines
  , tExtra     :: Int          -- ^ predicted lines with no truth counterpart
  , tDeps      :: (Int, Int)   -- ^ (correct, total) per column
  , tNum       :: (Int, Int)
  , tFormula   :: (Int, Int)
  , tJust      :: (Int, Int)
  , tVerdictOK :: Bool
  , tTruthVerdict :: Verdict
  , tPredVerdict  :: Verdict
  }

--------------------------------------------------------------------------------
-- Scoring
--------------------------------------------------------------------------------

byLine :: Proof -> M.Map Int ProofLine
byLine p = M.fromList [ (lineNumber l, l) | l <- p ]

-- Compare a truth line against a prediction. Parsed values are used when both
-- sides parsed — so "P->Q" and "P→Q" count as equal — and raw text otherwise.
score :: Side -> Side -> Tally
score truth pred_ =
  let tCells = sCells truth
      pCells = sCells pred_
      semantic = case (sProof truth, sProof pred_) of
        (Just tp, Just pp) -> Just (byLine tp, byLine pp)
        _                  -> Nothing

      keys = M.keys tCells
      n    = length keys

      cmp k =
        case M.lookup k pCells of
          Nothing -> (0, 0, 0, 0)
          Just pc ->
            let tc = tCells M.! k
            in case semantic of
                 Just (tm, pm)
                   | Just tl <- M.lookup (read k) tm
                   , Just pl <- M.lookup (read k) pm ->
                       ( b (references    tl == references    pl)
                       , 1
                       , b (formula       tl == formula       pl)
                       , b (justification tl == justification pl) )
                 -- Whole-proof parsing failed, but individual cells can
                 -- still be compared on their merits rather than as text.
                 _ ->
                       ( b (sameDeps    (tc !! 0) (pc !! 0))
                       , 1
                       , b (sameFormula (tc !! 2) (pc !! 2))
                       , b (tc !! 3 == pc !! 3) )

      cells = map cmp keys
      b True  = 1
      b False = 0
      sum4 f  = sum (map f cells)
      tv = verdictOf truth
      pv = verdictOf pred_
  in Tally
       { tLines        = n
       , tExtra        = length [ () | k <- M.keys pCells, not (M.member k tCells) ]
       , tDeps         = (sum4 (\(a,_,_,_) -> a), n)
       , tNum          = (sum4 (\(_,a,_,_) -> a), n)
       , tFormula      = (sum4 (\(_,_,a,_) -> a), n)
       , tJust         = (sum4 (\(_,_,_,a) -> a), n)
       , tVerdictOK    = tv == pv
       , tTruthVerdict = tv
       , tPredVerdict  = pv
       }

-- Compare two dependency cells as sets, so "2,1" and "1,2" agree.
sameDeps :: String -> String -> Bool
sameDeps a c = norm a == norm c
  where norm = sort . filter (not . null) . splitCommas
        splitCommas s = case break (== ',') s of
          (x, [])     -> [trimSp x]
          (x, _:rest) -> trimSp x : splitCommas rest
        trimSp = dropWhile (== ' ') . reverse . dropWhile (== ' ') . reverse

-- Compare two formula cells by parsing them individually. Falls back to text
-- when a cell will not parse, which is itself a meaningful difference.
sameFormula :: String -> String -> Bool
sameFormula a c =
  case (pf a, pf c) of
    (Right x, Right y) -> x == y
    _                  -> a == c
  where pf = parseFormula . normalizeFormula

-- A missing prediction still contributes its truth lines to the denominator,
-- and cannot agree on the verdict.
zeroTally :: Side -> Tally
zeroTally truth =
  let n  = M.size (sCells truth)
      tv = verdictOf truth
      pv = if tv == VValid then VInvalid else VValid
  in Tally n 0 (0,n) (0,n) (0,n) (0,n) False tv pv

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  args <- getArgs
  (truthDir, predDir) <- case args of
    [t, p] -> pure (t, p)
    _      -> die "usage: eval-score <truth-dir> <pred-dir>"

  names <- sort . filter (".pipe" `isSuffixOf`) <$> listDirectory truthDir
  unless (not (null names)) $ die ("no .pipe files in " ++ truthDir)

  results <- forM names $ \nm -> do
    truth <- readSide <$> readFile (truthDir </> nm)
    let predPath = predDir </> nm
    have <- doesFileExist predPath
    if not have
      then pure (nm, truth, Missing)
      else do
        p <- readSide <$> readFile predPath
        pure (nm, truth, Scored (score truth p))

  putStrLn ""
  printf "%-14s %6s %7s %7s %7s %7s   %s\n"
         "file" "lines" "deps" "line" "formula" "just" "verdict"
  putStrLn (replicate 78 '-')

  let tallies = [ (nm, t, o) | (nm, t, o) <- results ]
  mapM_ report tallies

  let ts = [ tallyOf t o | (_, t, o) <- tallies ]
      agg f = (sum (map (fst . f) ts), sum (map (snd . f) ts))
      verdictOK = length (filter tVerdictOK ts)
      nfiles    = length ts
  putStrLn (replicate 78 '-')
  printf "%-14s %6d %7s %7s %7s %7s   %d/%d\n"
         "TOTAL" (sum (map tLines ts))
         (pct (agg tDeps)) (pct (agg tNum)) (pct (agg tFormula)) (pct (agg tJust))
         verdictOK nfiles
  putStrLn ""
  printf "cell accuracy   %s over %d cells\n"
         (pct (agg4 ts)) (4 * sum (map tLines ts))
  printf "verdict agreement %d/%d files\n" verdictOK nfiles
  putStrLn ""
  if verdictOK == nfiles then exitSuccess else exitFailure
  where
    tallyOf t o = case o of
      Scored x  -> x
      Missing   -> zeroTally t

    report (nm, t, o) = case o of
      Missing       -> printf "%-14s %6d %7s %7s %7s %7s   %s\n"
                              nm (M.size (sCells t)) "-" "-" "-" "-"
                              ("MISSING" :: String)
      Scored x      -> printf "%-14s %6d %7s %7s %7s %7s   %s\n"
                              nm (tLines x)
                              (pct (tDeps x)) (pct (tNum x))
                              (pct (tFormula x)) (pct (tJust x))
                              (verdictNote x)

    verdictNote x
      | tVerdictOK x = "ok (" ++ showVerdict (tTruthVerdict x) ++ ")"
      | otherwise    = "MISMATCH truth=" ++ showVerdict (tTruthVerdict x)
                       ++ " pred=" ++ showVerdict (tPredVerdict x)

    agg4 ts = ( sum [ c | t <- ts, (c,_) <- [tDeps t, tNum t, tFormula t, tJust t] ]
              , sum [ n | t <- ts, (_,n) <- [tDeps t, tNum t, tFormula t, tJust t] ] )

pct :: (Int, Int) -> String
pct (_, 0) = "-"
pct (a, b) = printf "%.0f%%" (100 * fromIntegral a / fromIntegral b :: Double)

firstLine :: String -> String
firstLine s = case lines s of
  (l:_) -> take 40 l
  []    -> s
