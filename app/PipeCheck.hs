-- app/PipeCheck.hs
--
-- Read a proof in pipe format (from a file argument or stdin), check it, and
-- print a JSON report.
--
-- Parsing lives in the PipeParse library module, which is also what the web
-- front end uses. This executable previously carried its own copy of the
-- justification parser; the copy drifted out of step with the library and
-- silently lost support for RAA, =I, =E, LEM, prop taut, ↔I and ↔E, as well
-- as the ASCII-shorthand normalisation applied to the formula column.
-- Sharing one parser is what keeps this exe and the web app agreeing about
-- what a proof is.

{-# LANGUAGE OverloadedStrings #-}

module Main where

import           ProofTypes
import           PipeParse                   (parsePipeProof)
import           PrettyPrint                 (renderFormula)
import           LemmonChecker               (checkProof, proofValid, LineReport(..))

import           Data.Aeson                  (Value(..), (.=), object, encode)
import qualified Data.ByteString.Lazy.Char8 as BL
import qualified Data.Set                   as S

import           System.Environment          (getArgs)

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
    []     -> getContents
    (fp:_) -> readFile fp

  case parsePipeProof input of
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
