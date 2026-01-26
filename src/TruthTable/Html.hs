{-# LANGUAGE OverloadedStrings #-}

module TruthTable.Html
  ( truthTableHtml
  , truthTableHtmlMainOnly
  ) where

import TruthTable (TruthTableData(..), TTToken(..), TTRow(..), Tok(..))
import TruthTable.Style (TruthStyle, truthText)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)
import Text.Blaze.Html5 as H
import Text.Blaze.Html5.Attributes as A

-- display tokens in the header row
tokHeaderText :: TruthStyle -> Tok -> String
tokHeaderText _  TLParen        = "("
tokHeaderText _  TRParen        = ")"
tokHeaderText _  TNot           = "¬"
tokHeaderText _  TAnd           = "∧"
tokHeaderText _  TOr            = "∨"
tokHeaderText _  TImpl          = "→"
tokHeaderText _  TIff           = "↔"
tokHeaderText _  (TAtom p)      = p
tokHeaderText st (TConst True)  = truthText st True
tokHeaderText st (TConst False) = truthText st False

-- blank for parens, otherwise chosen truth glyphs
tokValCellText :: TruthStyle -> TTToken -> Maybe Bool -> String
tokValCellText _  (TTToken TLParen Nothing) _ = ""
tokValCellText _  (TTToken TRParen Nothing) _ = ""
tokValCellText _  _ Nothing                   = ""
tokValCellText st _ (Just b)                  = truthText st b

truthTableHtml :: TruthStyle -> TruthTableData -> Html
truthTableHtml st tt =
  H.table ! A.class_ "tt" $ do
    thead $ tr $ do
      mapM_ (\p -> th (toHtml p)) (ttProps tt)
      let toks = ttTokens tt
      mapM_ (uncurry (tokTh st (ttMainIx tt))) (zip [0..] toks)

    tbody $ mapM_ (rowTr st tt (Just [0 .. length (ttTokens tt) - 1])) (ttRows tt)

truthTableHtmlMainOnly :: TruthStyle -> TruthTableData -> Html
truthTableHtmlMainOnly st tt =
  H.table ! A.class_ "tt" $ do
    thead $ tr $ do
      mapM_ (\p -> th (toHtml p)) (ttProps tt)
      tokTh st (ttMainIx tt) (ttMainIx tt) (ttTokens tt !! ttMainIx tt)

    tbody $ mapM_ (rowTr st tt (Just [ttMainIx tt])) (ttRows tt)

tokTh :: TruthStyle -> Int -> Int -> TTToken -> Html
tokTh st mainIx i (TTToken sym _) =
  let cls0 = "tok tokhead"
      cls1 = if i == 0      then cls0 ++ " divider-left" else cls0
      cls2 = if i == mainIx then cls1 ++ " maincol"      else cls1
  in th ! A.class_ (toValue cls2) $ toHtml (tokHeaderText st sym)

rowTr :: TruthStyle -> TruthTableData -> Maybe [Int] -> TTRow -> Html
rowTr st tt mCols r =
  tr $ do
    mapM_ (propTd st r) (ttProps tt)
    let cols = fromMaybe [0..length (ttTokens tt)-1] mCols
    mapM_ (tokTd st tt r) cols

propTd :: TruthStyle -> TTRow -> String -> Html
propTd st r p =
  let b = fromMaybe False (M.lookup p (rowValuation r))
  in td ! A.class_ "valTF" $ toHtml (truthText st b)

tokTd :: TruthStyle -> TruthTableData -> TTRow -> Int -> Html
tokTd st tt r i =
  let t  = ttTokens tt !! i
      mv = rowTokVals r !! i
      cls0 = "tok"
      cls1 = if i == 0           then cls0 ++ " divider-left" else cls0
      cls2 = if i == ttMainIx tt then cls1 ++ " maincol"      else cls1
  in td ! A.class_ (toValue cls2) $
       toHtml (tokValCellText st t mv)

