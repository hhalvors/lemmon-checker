{-# LANGUAGE OverloadedStrings #-}

module TruthTable.LaTeX
  ( renderTruthTableLaTeX
  ) where

import TruthTable (TruthTableData(..), TTToken(..), Tok(..), TTRow(..))
import TruthTable.Style (TruthStyle, truthLaTeX)
import Data.List (intercalate)
import qualified Data.Map.Strict as M

renderTruthTableLaTeX :: TruthStyle -> TruthTableData -> String
renderTruthTableLaTeX st tt =
  unlines $
    [ "% NOTE: requires \\usepackage{array}"
    , "\\begin{tabular}{" ++ colSpec tt ++ "}"
    , headerRow st tt ++ " \\\\"
    , "\\hline"
    ]
    ++ map (\r -> dataRow st tt r ++ " \\\\") (ttRows tt)
    ++ [ "\\end{tabular}" ]

--------------------------------------------------------------------------------
-- Column spec
--------------------------------------------------------------------------------

colSpec :: TruthTableData -> String
colSpec tt =
  let nProps = length (ttProps tt)
      propCols = replicate nProps "c"
      tokCols  = map tokCol (ttTokens tt)
  in intercalate "" $
       propCols ++ ["|"] ++ tokCols
  where
    tokCol (TTToken TLParen Nothing) = "@{}c@{}"
    tokCol (TTToken TRParen Nothing) = "@{}c@{}"
    tokCol _                         = "@{ }c@{ }"

--------------------------------------------------------------------------------
-- Rows
--------------------------------------------------------------------------------

headerRow :: TruthStyle -> TruthTableData -> String
headerRow st tt =
  let props = map (\p -> "$" ++ escapeMath p ++ "$") (ttProps tt)
      toks  = map (\t -> "$" ++ tokHeader st t ++ "$") (ttTokens tt)
  in join (props ++ toks)

dataRow :: TruthStyle -> TruthTableData -> TTRow -> String
dataRow st tt r =
  let props = map (\p -> "$" ++ truthLaTeX st (lookupProp p) ++ "$") (ttProps tt)
      toks  = zipWith (tokCell st) (ttTokens tt) (rowTokVals r)
  in join (props ++ toks)
  where
    lookupProp p =
      case M.lookup p (rowValuation r) of
        Just b  -> b
        Nothing -> False

--------------------------------------------------------------------------------
-- Token rendering
--------------------------------------------------------------------------------

tokHeader :: TruthStyle -> TTToken -> String
tokHeader _  (TTToken TLParen Nothing) = "("
tokHeader _  (TTToken TRParen Nothing) = ")"
tokHeader _  (TTToken TNot  _)         = "\\neg"
tokHeader _  (TTToken TAnd  _)         = "\\wedge"
tokHeader _  (TTToken TOr   _)         = "\\vee"
tokHeader _  (TTToken TImpl _)         = "\\to"
tokHeader _  (TTToken TIff  _)         = "\\leftrightarrow"
tokHeader _  (TTToken (TAtom p) _)     = escapeMath p
tokHeader st (TTToken (TConst True) _)  = truthLaTeX st True
tokHeader st (TTToken (TConst False) _) = truthLaTeX st False

tokCell :: TruthStyle -> TTToken -> Maybe Bool -> String
tokCell _  (TTToken TLParen Nothing) _ = "$\\,$"
tokCell _  (TTToken TRParen Nothing) _ = "$\\,$"
tokCell _  _ Nothing                   = "$\\,$"
tokCell st _ (Just b)                  = "$" ++ truthLaTeX st b ++ "$"

--------------------------------------------------------------------------------

join :: [String] -> String
join = intercalate " & "

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


