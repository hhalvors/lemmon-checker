{-# LANGUAGE OverloadedStrings #-}

module TruthTable.Html
  ( truthTableHtml
  , truthTableHtmlMainOnly
  ) where

import TruthTable (TruthTableData(..), TTToken(..), TTRow(..), Tok(..))
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)
import Text.Blaze.Html5 as H
import Text.Blaze.Html5.Attributes as A

-- display tokens in the header row
tokHeaderText :: Tok -> String
tokHeaderText TLParen      = "("
tokHeaderText TRParen      = ")"
tokHeaderText TNot         = "¬"
tokHeaderText TAnd         = "∧"
tokHeaderText TOr          = "∨"
tokHeaderText TImpl        = "→"
tokHeaderText TIff         = "↔"
tokHeaderText (TAtom p)    = p
tokHeaderText (TConst True)  = "⊤"
tokHeaderText (TConst False) = "⊥"

tf :: Bool -> String
tf True  = "T"
tf False = "F"

-- blank for parens, otherwise T/F
tokValCellText :: TTToken -> Maybe Bool -> String
tokValCellText (TTToken TLParen Nothing) _ = ""
tokValCellText (TTToken TRParen Nothing) _ = ""
tokValCellText _ Nothing                   = ""
tokValCellText _ (Just b)                  = tf b

-- Full token table (props + all token columns)
truthTableHtml :: TruthTableData -> Html
truthTableHtml tt =
  H.table ! A.class_ "tt" $ do
    thead $ tr $ do
      -- proposition headers
      mapM_ (\p -> th (toHtml p)) (ttProps tt)

      -- token headers (thick divider on first token col)
      let toks = ttTokens tt
      mapM_ (uncurry (tokTh (ttMainIx tt))) (zip [0..] toks)

    tbody $ mapM_ (rowTr tt (Just [0 .. length (ttTokens tt) - 1])) (ttRows tt)

-- Main connective only (props + that one token column)
truthTableHtmlMainOnly :: TruthTableData -> Html
truthTableHtmlMainOnly tt =
  H.table ! A.class_ "tt" $ do
    thead $ tr $ do
      mapM_ (\p -> th (toHtml p)) (ttProps tt)
      tokTh (ttMainIx tt) (ttMainIx tt) (ttTokens tt !! ttMainIx tt)

    tbody $ mapM_ (rowTr tt (Just [ttMainIx tt])) (ttRows tt)

tokTh :: Int -> Int -> TTToken -> Html
tokTh mainIx i (TTToken sym _) =
  let cls0 = "tok tokhead"
      cls1 = if i == 0      then cls0 ++ " divider-left" else cls0
      cls2 = if i == mainIx then cls1 ++ " maincol"      else cls1
  in th ! A.class_ (toValue cls2) $ toHtml (tokHeaderText sym)    

rowTr :: TruthTableData -> Maybe [Int] -> TTRow -> Html
rowTr tt mCols r =
  tr $ do
    -- left valuation columns: plain T/F (NOT math)
    mapM_ (propTd r) (ttProps tt)

    let cols = fromMaybe [0..length (ttTokens tt)-1] mCols
    mapM_ (tokTd tt r) cols

propTd :: TTRow -> String -> Html
propTd r p =
  let b = fromMaybe False (M.lookup p (rowValuation r))
  in td ! A.class_ "valTF" $ toHtml (tf b)

tokTd :: TruthTableData -> TTRow -> Int -> Html
tokTd tt r i =
  let t  = ttTokens tt !! i
      mv = rowTokVals r !! i

      cls0 = "tok"
      cls1 = if i == 0           then cls0 ++ " divider-left" else cls0
      cls2 = if i == ttMainIx tt then cls1 ++ " maincol"      else cls1
  in td ! A.class_ (toValue cls2) $
       toHtml (tokValCellText t mv)  

