-- app/PipeToJson.hs
--
-- Read a proof in pipe format (from a file argument or stdin) and emit it as
-- Proof JSON on stdout.
--
-- Parsing lives in the PipeParse library module, shared with the web front
-- end and with pipe-check. The local copy this file used to carry had drifted
-- from the library: it lagged behind a change to the ForallIntro constructor
-- (so the executable no longer compiled at all) and never gained RAA, =I, =E,
-- LEM, QN, prop taut, ↔I or ↔E.

{-# LANGUAGE OverloadedStrings #-}

module Main where

import           PipeParse                   (parsePipeProof)

import           Data.Aeson                  (encode)
import qualified Data.ByteString.Lazy.Char8 as BL

import           System.Environment          (getArgs)
import           System.Exit                 (die)
import           System.IO                   (hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  input <- case args of
    []     -> getContents
    (fp:_) -> readFile fp

  case parsePipeProof input of
    Left err -> do
      hPutStrLn stderr err
      hPutStrLn stderr "\nHere is the input:\n"
      hPutStrLn stderr input
      die ""
    Right proof ->
      BL.putStrLn (encode proof)
