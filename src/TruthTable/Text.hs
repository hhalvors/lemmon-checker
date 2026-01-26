module TruthTable.Text (renderTruthTableText) where

import TruthTable
import TruthTable.Style (TruthStyle, truthText)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)

tokChar :: TruthStyle -> Tok -> String
tokChar _  TLParen        = "("
tokChar _  TRParen        = ")"
tokChar _  TNot           = "¬"
tokChar _  TAnd           = "∧"
tokChar _  TOr            = "∨"
tokChar _  TImpl          = "→"
tokChar _  TIff           = "↔"
tokChar _  (TAtom p)      = p
tokChar st (TConst True)  = truthText st True
tokChar st (TConst False) = truthText st False

-- Force every printed cell to be exactly one visible column:
cell1 :: String -> String
cell1 ""    = " "
cell1 [c]   = [c]
cell1 (c:_) = [c]   -- should never happen if your invariants hold

tokVal :: TruthStyle -> TTToken -> Maybe Bool -> String
tokVal _  (TTToken TLParen Nothing) _ = " "
tokVal _  (TTToken TRParen Nothing) _ = " "
tokVal _  _ Nothing                   = " "
tokVal st _ (Just b)                  = truthText st b

renderTruthTableText :: TruthStyle -> TruthTableData -> String
renderTruthTableText st tt =
  unlines (hdr : rule : map rowLine (ttRows tt))
  where
    propsHdr  = map cell1 (ttProps tt)
    toksHdr   = map (cell1 . tokChar st . tokSym) (ttTokens tt)

    hdr =
      unwords propsHdr ++ " | " ++ unwords toksHdr

    rule = replicate (length hdr) '-'

    rowLine r =
      let left =
            [ cell1 (truthText st (fromMaybe False (M.lookup p (rowValuation r))))
            | p <- ttProps tt
            ]
          mid =
            zipWith (\t v -> cell1 (tokVal st t v)) (ttTokens tt) (rowTokVals r)
      in unwords left ++ " | " ++ unwords mid


