module TruthTable.Text (renderTruthTableText) where

import TruthTable
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)
import Data.List (intercalate)

tf :: Bool -> String
tf True  = "T"
tf False = "F"

tokChar :: Tok -> String
tokChar TLParen       = "("
tokChar TRParen       = ")"
tokChar TNot          = "¬"
tokChar TAnd          = "∧"
tokChar TOr           = "∨"
tokChar TImpl         = "→"
tokChar TIff          = "↔"
tokChar (TAtom p)     = p
tokChar (TConst True)  = "⊤"
tokChar (TConst False) = "⊥"

tokVal :: TTToken -> Maybe Bool -> String
tokVal (TTToken TLParen Nothing) _ = ""
tokVal (TTToken TRParen Nothing) _ = ""
tokVal _ Nothing                   = ""
tokVal _ (Just b)                  = tf b

renderTruthTableText :: TruthTableData -> String
renderTruthTableText tt =
  unlines (hdr : map rowLine (ttRows tt))
  where
    hdr =
      intercalate " " (ttProps tt ++ map (tokChar . tokSym) (ttTokens tt))

    rowLine r =
      let left = [ tf (fromMaybe False (M.lookup p (rowValuation r))) | p <- ttProps tt ]
          mid  = zipWith tokVal (ttTokens tt) (rowTokVals r)
      in intercalate " " (left ++ mid)
