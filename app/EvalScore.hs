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
import           LemmonChecker      (checkProof, proofValid)

import qualified Data.Map.Strict   as M
import           Data.List          (sort, isSuffixOf, intercalate)
import           Control.Monad      (forM, unless)
import           System.Directory   (listDirectory, doesFileExist)
import           System.Environment (getArgs)
import           System.Exit        (die, exitFailure, exitSuccess)
import           System.FilePath    ((</>))
import           Text.Printf        (printf)

--------------------------------------------------------------------------------
-- Per-file result
--------------------------------------------------------------------------------

data Outcome
  = Missing              -- ^ no prediction file at all
  | Unparseable String   -- ^ prediction present but not parseable
  | Scored Tally

data Tally = Tally
  { tLines     :: Int          -- ^ truth lines
  , tExtra     :: Int          -- ^ predicted lines with no truth counterpart
  , tDeps      :: (Int, Int)   -- ^ (correct, total) per column
  , tNum       :: (Int, Int)
  , tFormula   :: (Int, Int)
  , tJust      :: (Int, Int)
  , tVerdictOK :: Bool
  , tTruthVerdict :: Bool
  , tPredVerdict  :: Bool
  }

--------------------------------------------------------------------------------
-- Scoring
--------------------------------------------------------------------------------

byLine :: Proof -> M.Map Int ProofLine
byLine p = M.fromList [ (lineNumber l, l) | l <- p ]

score :: Proof -> Proof -> Tally
score truth pred_ =
  let tm = byLine truth
      pm = byLine pred_
      -- A truth line with no prediction scores zero on all four cells; the
      -- line-number cell is credited only when the line was found at all.
      cells = [ cmp t (M.lookup n pm) | (n, t) <- M.toList tm ]
      cmp t mp = case mp of
        Nothing -> (0, 0, 0, 0)
        Just p  ->
          ( b (references    t == references    p)
          , 1
          , b (formula       t == formula       p)
          , b (justification t == justification p) )
      b True  = 1
      b False = 0
      sum4 f = sum [ f c | c <- cells ]
      n      = M.size tm
      tv     = proofValid (checkProof truth)
      pv     = proofValid (checkProof pred_)
  in Tally
       { tLines        = n
       , tExtra        = length [ () | k <- M.keys pm, not (M.member k tm) ]
       , tDeps         = (sum4 (\(a,_,_,_) -> a), n)
       , tNum          = (sum4 (\(_,a,_,_) -> a), n)
       , tFormula      = (sum4 (\(_,_,a,_) -> a), n)
       , tJust         = (sum4 (\(_,_,_,a) -> a), n)
       , tVerdictOK    = tv == pv
       , tTruthVerdict = tv
       , tPredVerdict  = pv
       }

-- A file with no usable prediction still contributes its truth lines to the
-- denominator, and counts as a verdict disagreement.
zeroTally :: Proof -> Tally
zeroTally truth =
  let n  = length truth
      tv = proofValid (checkProof truth)
  in Tally n 0 (0,n) (0,n) (0,n) (0,n) False tv (not tv)

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
    truthTxt <- readFile (truthDir </> nm)
    truth <- case parsePipeProof truthTxt of
      Left e  -> die ("truth file " ++ nm ++ " does not parse: " ++ e)
      Right p -> pure p
    let predPath = predDir </> nm
    have <- doesFileExist predPath
    if not have
      then pure (nm, truth, Missing)
      else do
        predTxt <- readFile predPath
        case parsePipeProof predTxt of
          Left e  -> pure (nm, truth, Unparseable (firstLine e))
          Right p -> pure (nm, truth, Scored (score truth p))

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
      Scored x       -> x
      Missing        -> zeroTally t
      Unparseable _  -> zeroTally t

    report (nm, t, o) = case o of
      Missing       -> printf "%-14s %6d %7s %7s %7s %7s   %s\n"
                              nm (length t) "-" "-" "-" "-" ("MISSING" :: String)
      Unparseable e -> printf "%-14s %6d %7s %7s %7s %7s   %s\n"
                              nm (length t) "-" "-" "-" "-" ("PARSE: " ++ e)
      Scored x      -> printf "%-14s %6d %7s %7s %7s %7s   %s\n"
                              nm (tLines x)
                              (pct (tDeps x)) (pct (tNum x))
                              (pct (tFormula x)) (pct (tJust x))
                              (verdictNote x)

    verdictNote x
      | tVerdictOK x = "ok (" ++ vs (tTruthVerdict x) ++ ")"
      | otherwise    = "MISMATCH truth=" ++ vs (tTruthVerdict x)
                       ++ " pred=" ++ vs (tPredVerdict x)
    vs True  = "valid"
    vs False = "invalid"

    agg4 ts = ( sum [ c | t <- ts, (c,_) <- [tDeps t, tNum t, tFormula t, tJust t] ]
              , sum [ n | t <- ts, (_,n) <- [tDeps t, tNum t, tFormula t, tJust t] ] )

pct :: (Int, Int) -> String
pct (_, 0) = "-"
pct (a, b) = printf "%.0f%%" (100 * fromIntegral a / fromIntegral b :: Double)

firstLine :: String -> String
firstLine s = case lines s of
  (l:_) -> take 40 l
  []    -> s
