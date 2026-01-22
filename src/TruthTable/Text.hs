module TruthTable.Text (renderTruthTableText) where

import TruthTable
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)
import Data.List (intercalate)

tf :: Bool -> String
tf True  = "T"
tf False = "F"

tokChar :: Tok -> String
tokChar TLParen        = "("
tokChar TRParen        = ")"
tokChar TNot           = "¬"
tokChar TAnd           = "∧"
tokChar TOr            = "∨"
tokChar TImpl          = "→"
tokChar TIff           = "↔"
tokChar (TAtom p)      = p
tokChar (TConst True)  = "⊤"
tokChar (TConst False) = "⊥"

-- Force every printed cell to be exactly one visible column:
cell1 :: String -> String
cell1 ""    = " "
cell1 [c]   = [c]
cell1 (c:_) = [c]   -- should never happen if your invariants hold

tokVal :: TTToken -> Maybe Bool -> String
tokVal (TTToken TLParen Nothing) _ = " "
tokVal (TTToken TRParen Nothing) _ = " "
tokVal _ Nothing                   = " "
tokVal _ (Just b)                  = tf b

renderTruthTableText :: TruthTableData -> String
renderTruthTableText tt =
  unlines (hdr : rule : map rowLine (ttRows tt))
  where
    propsHdr  = map cell1 (ttProps tt)
    toksHdr   = map (cell1 . tokChar . tokSym) (ttTokens tt)

    hdr =
      unwords propsHdr ++ " | " ++ unwords toksHdr

    -- simple horizontal rule (keep it purely "-" like Rieppel)
    rule = replicate (length hdr) '-'

    rowLine r =
      let left =
            [ cell1 (tf (fromMaybe False (M.lookup p (rowValuation r))))
            | p <- ttProps tt
            ]
          mid =
            zipWith (\t v -> cell1 (tokVal t v)) (ttTokens tt) (rowTokVals r)
      in unwords left ++ " | " ++ unwords mid

