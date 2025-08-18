{-# LANGUAGE OverloadedStrings #-}

module Main where

import ProofTypes
import PrettyPrint (renderFormula)
import qualified Data.Set as S
import Data.Aeson (eitherDecode)
import qualified Data.ByteString.Lazy as BL
import Data.List (intercalate)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import System.Environment (getArgs)

ppDepends :: S.Set Int -> String
ppDepends = intercalate "," . map show . S.toAscList

-- turn a Justification into a compact rightmost-column string
ppJust :: Justification -> String
ppJust j = case j of
  Assumption           -> "A"
  MP i j'              -> two "MP" i j'
  MT i j'              -> two "MT" i j'
  DN i                 -> one "DN" i
  CP i j'              -> two "CP" i j'
  AndIntro i j'        -> two "∧I" i j'
  AndElim i            -> one "∧E" i
  OrIntro i            -> one "∨I" i
  OrElim a b c d e     -> list "∨E" [a,b,c,d,e]
  RAA i j'             -> two "RAA" i j'
  ForallElim i         -> one "∀E" i
  ExistsIntro i        -> one "∃I" i
  ForallIntro i _x     -> one "∀I" i
  ExistsElim m m1 n    -> list "∃E" [m,m1,n]
  where
    one tag i         = show i <> " " <> tag
    two tag i j'      = show i <> "," <> show j' <> " " <> tag
    list tag xs       = intercalate "," (map show xs) <> " " <> tag

ppLine :: ProofLine -> String
ppLine l = intercalate "|"
  [ ppDepends (references l)
  , show (lineNumber l)
  , renderFormula (formula l)
  , ppJust (justification l)
  ]

main :: IO ()
main = do
  args <- getArgs
  bytes <- case args of
    [fp] -> BL.readFile fp
    _    -> BL.getContents
  case eitherDecode bytes :: Either String Proof of
    Left err   -> putStrLn ("JSON decode error: " <> err)
    Right prf  -> do
      T.putStrLn "PROOF"
      mapM_ (T.putStrLn . T.pack . ppLine) prf
