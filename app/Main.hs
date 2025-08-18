-- Main.hs
module Main where

import LemmonChecker (checkProof, printReport, proofValid)   -- new exports
import Data.Aeson        (eitherDecode)
import qualified Data.ByteString.Lazy as B
import System.Environment (getArgs)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [filename] -> do
      putStrLn $ "🔍 Attempting to read " ++ filename ++ "..."
      raw <- B.readFile filename
      case eitherDecode raw of
        Left err   -> putStrLn $ "❌ JSON parse error:\n" ++ err
        Right p -> do
          putStrLn "✅ Parsed successfully.  Checking proof…"
          let report = checkProof p       -- ProofReport
          printReport report              -- pretty table
          putStrLn $
            if proofValid report
               then "\n🎉  Overall result: proof is VALID."
               else "\n🚫  Overall result: proof is INVALID."
    _ -> putStrLn "Usage:  lemmon-check <proof.json>"
