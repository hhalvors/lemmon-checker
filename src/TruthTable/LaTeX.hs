{-# LANGUAGE OverloadedStrings #-}

module TruthTable.LaTeX
  ( renderTruthTableLaTeX
  ) where

import TruthTable (TruthTableData(..), TTToken(..), Tok(..), TTRow(..))
import Data.List (intercalate)
import qualified Data.Map.Strict as M

renderTruthTableLaTeX :: TruthTableData -> String
renderTruthTableLaTeX tt =
  unlines $
    [ "% NOTE: requires \\usepackage{array}"
    , "\\begin{tabular}{" ++ colSpec tt ++ "}"
    , headerRow tt ++ " \\\\"
    , "\\hline"
    ]
    ++ map (\r -> dataRow tt r ++ " \\\\") (ttRows tt)
    ++ [ "\\end{tabular}" ]

--------------------------------------------------------------------------------
-- Column spec
--------------------------------------------------------------------------------

-- We keep it simple and robust:
--   c c c | c c c c ...
-- and we “squeeze” parentheses with @{} on both sides.
colSpec :: TruthTableData -> String
colSpec tt =
  let nProps = length (ttProps tt)
      propCols = replicate nProps "c"
      tokCols  = map tokCol (ttTokens tt)
  in intercalate "" $
       map (++ "") propCols
       ++ ["|"]
       ++ tokCols
  where
    tokCol (TTToken TLParen Nothing) = "@{}c@{}"
    tokCol (TTToken TRParen Nothing) = "@{}c@{}"
    tokCol _                         = "@{ }c@{ }"

--------------------------------------------------------------------------------
-- Rows
--------------------------------------------------------------------------------

headerRow :: TruthTableData -> String
headerRow tt =
  let props = map (\p -> "$" ++ escapeMath p ++ "$") (ttProps tt)
      toks  = map (\t -> "$" ++ tokHeader t ++ "$") (ttTokens tt)
  in join (props ++ toks)

dataRow :: TruthTableData -> TTRow -> String
dataRow tt r =
  let props = map (\p -> "$" ++ tf (lookupProp p) ++ "$") (ttProps tt)
      toks  = zipWith tokCell (ttTokens tt) (rowTokVals r)
  in join (props ++ toks)
  where
    lookupProp p =
      case M.lookup p (rowValuation r) of
        Just b  -> b
        Nothing -> False

-- Avoid importing Map stuff in this module: use a tiny local view
toList :: (Foldable t) => t a -> [a]
toList = foldr (:) []

--------------------------------------------------------------------------------
-- Token rendering
--------------------------------------------------------------------------------

tokHeader :: TTToken -> String
tokHeader (TTToken TLParen Nothing) = "("
tokHeader (TTToken TRParen Nothing) = ")"
tokHeader (TTToken TNot  _)         = "\\neg"
tokHeader (TTToken TAnd  _)         = "\\wedge"
tokHeader (TTToken TOr   _)         = "\\vee"
tokHeader (TTToken TImpl _)         = "\\to"
tokHeader (TTToken TIff  _)         = "\\leftrightarrow"
tokHeader (TTToken (TAtom p) _)     = escapeMath p
tokHeader (TTToken (TConst True) _) = "\\top"
tokHeader (TTToken (TConst False) _) = "\\bot"

tokCell :: TTToken -> Maybe Bool -> String
tokCell (TTToken TLParen Nothing) _ = "$\\,$"   -- blank
tokCell (TTToken TRParen Nothing) _ = "$\\,$"   -- blank
tokCell _ Nothing                   = "$\\,$"   -- blank (safety)
tokCell _ (Just b)                  = "$" ++ tf b ++ "$"

tf :: Bool -> String
tf True  = "\\top"
tf False = "\\bot"

join :: [String] -> String
join = intercalate " & "

-- Escape token text inside math mode (very light touch)
escapeMath :: String -> String
escapeMath = concatMap go
  where
    go '_'  = "\\_"
    go '#'  = "\\#"
    go '&'  = "\\&"
    go '%'  = "\\%"
    go '$'  = "\\$"
    go '{'  = "\\{"
    go '}'  = "\\}"
    go '^'  = "\\^{}"
    go '~'  = "\\~{}"
    go '\\' = "\\textbackslash{}"
    go c    = [c]

