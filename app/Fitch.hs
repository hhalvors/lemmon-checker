-- app/Fitch.hs
--
--   fitch < proof.pipe
--
-- Reads a Lemmon proof in pipe format, prints the Fitch presentation, and
-- then checks the round trip: translating the result back to Lemmon should
-- return the proof it started from, line for line.
--
-- The round trip is the real test here. A rendering can look plausible and
-- still be wrong; the round trip cannot. If Fitch → Lemmon recovers the
-- original dependency sets, then the box structure the translation invented
-- carries exactly the information the dependency sets did.
--
-- One asymmetry to expect: the recovered dependency sets are minimal, and a
-- Lemmon proof written by hand may cite more than it needs. Where the two
-- differ, the difference is reported rather than treated as failure, because
-- which of the two is "right" is a question about the source proof.

module Main where

import ProofTypes
import PipeParse    (parsePipeProof)
import FitchTypes   (renderFitch)
import FitchConvert (lemmonToFitch, fitchToLemmon, renderTranslationError,
                     Route(..))

import qualified Data.Set as S
import           Control.Monad (forM_, unless)
import           System.Exit   (exitFailure)

main :: IO ()
main = do
  src <- getContents
  case parsePipeProof src of
    Left err -> putStrLn ("Could not parse the proof:\n" ++ err) >> exitFailure
    Right prf ->
      case lemmonToFitch prf of
        Left e -> do
          putStrLn "This proof could not be translated.\n"
          putStrLn (renderTranslationError e)
          exitFailure
        Right (Direct, fp) -> do
          putStr (renderFitch fp)
          putStrLn ""
          report prf (fitchToLemmon fp)
        Right (ViaTree, fp) -> do
          putStrLn "(no line-for-line Fitch image; unfolded through a \
                   \derivation tree, so lines are renumbered and any line \
                   \used twice is derived twice)\n"
          putStr (renderFitch fp)
          putStrLn ""
          let back = fitchToLemmon fp
          putStrLn $ "recovered proof has " ++ show (length back)
                     ++ " lines, from " ++ show (length prf) ++ "."
          case (lastFormula prf, lastFormula back) of
            (Just a, Just b)
              | a == b    -> putStrLn "conclusion unchanged."
              | otherwise -> putStrLn "CONCLUSION CHANGED -- this is a bug."
            _             -> putStrLn "one of the proofs is empty."

-- | Compare the original proof with the one recovered through Fitch.
report :: Proof -> Proof -> IO ()
report before after = do
  let pairs = zip before after
  unless (length before == length after) $
    putStrLn $ "Round trip changed the number of lines: "
               ++ show (length before) ++ " -> " ++ show (length after)
  forM_ pairs $ \(a, b) -> do
    unless (lineNumber a == lineNumber b) $
      putStrLn $ "  line " ++ show (lineNumber a) ++ ": renumbered to "
                 ++ show (lineNumber b)
    unless (formula a == formula b) $
      putStrLn $ "  line " ++ show (lineNumber a) ++ ": formula changed"
    unless (justification a == justification b) $
      putStrLn $ "  line " ++ show (lineNumber a) ++ ": justification "
                 ++ show (justification a) ++ " -> " ++ show (justification b)
    unless (references a == references b) $
      putStrLn $ "  line " ++ show (lineNumber a) ++ ": dependencies "
                 ++ showSet (references a) ++ " -> " ++ showSet (references b)
                 ++ (if references b `S.isSubsetOf` references a
                       then "  (recovered set is smaller: the original cited \
                            \more than it used)"
                       else "  (recovered set is LARGER -- this is a bug)")
  putStrLn "round trip complete."
  where
    showSet s = "{" ++ unwords (map show (S.toList s)) ++ "}"

lastFormula :: Proof -> Maybe PredFormula
lastFormula p = case reverse p of
  []      -> Nothing
  (l : _) -> Just (formula l)
