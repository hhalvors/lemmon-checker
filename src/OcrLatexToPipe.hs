{-# LANGUAGE OverloadedStrings #-}
module OcrLatexToPipe
  ( latexTableToPipe  -- :: String -> Either String String
  ) where

import qualified Data.Text as T
import           Data.Text (Text)
import           Data.Char (isSpace, isDigit)

-- Public API
latexTableToPipe :: String -> Either String String
latexTableToPipe src0 =
  let src   = T.pack src0
      body  = takeTabularBody src
      rows  = extractRows body
      pipes = mapMaybe rowToPipe rows
  in if null pipes
        then Left "No parseable proof rows found."
        else Right . T.unpack $ T.intercalate "\n" pipes

-- --- minimal extraction ------------------------------------------------------

takeTabularBody :: Text -> Text
takeTabularBody t =
  case T.breakOn "\\begin{tabular" t of
    (_, rest) | T.null rest -> t
    (_, rest) ->
      let afterBrace = T.drop 1 $ T.dropWhile (/= '}') (T.drop (T.length "\\begin{tabular") rest)
      in fst $ T.breakOn "\\end{tabular}" afterBrace

-- split on LaTeX row end (“\\”), trim, and keep only lines with ‘&’
extractRows :: Text -> [Text]
extractRows =
    filter hasAmp
  . map (T.strip . dropTrailingBackslashes)
  . T.splitOn "\\\\"
  . stripNoise
  where
    hasAmp x = T.isInfixOf "&" x
    dropTrailingBackslashes x =
      let y = T.dropWhileEnd isSpace x
      in if T.isSuffixOf "\\\\" y then T.dropEnd 2 y else y

stripNoise :: Text -> Text
stripNoise =
    T.replace "\\hline" ""
  . T.replace "\\caption" ""
  . T.replace "\r" ""

-- --- per-row conversion ------------------------------------------------------

rowToPipe :: Text -> Maybe Text
rowToPipe row =
  let cells = take 4 $ map (T.strip . cleanCell) (T.splitOn "&" row) ++ repeat ""
      [deps0, ln0, form0, just0] = cells
      deps = cleanupDeps deps0
      ln   = cleanupLine ln0
      form = normalizeLogic form0
      just = normalizeLogic just0
  in if isHeader cells || T.null form
       then Nothing
       else Just $ T.intercalate " | " [deps, ln, form, just]

isHeader :: [Text] -> Bool
isHeader cols =
  let x = T.toLower (T.intercalate " " cols)
  in any (`T.isInfixOf` x) ["depends","line","formula","justification"]

-- --- light cleanup + replacements -------------------------------------------

cleanCell :: Text -> Text
cleanCell =
    tidy
  . stripMath     -- remove $, \(...\), \[...\]
  . dropSimpleCmd "{mathrm}"
  . dropSimpleCmd "{text}"
  . dropSimpleCmd "{mathbb}"
  . stripBraces   -- remove all { }
  . tidy
  where
    tidy = T.unwords . T.words

stripMath :: Text -> Text
stripMath =
    T.replace "\\(" "" . T.replace "\\)" ""
  . T.replace "\\[" "" . T.replace "\\]" ""
  . T.replace "$$" ""  . T.replace "$"  ""

-- Drop occurrences like \mathrm{...} by just deleting the command name, keeping payload.
dropSimpleCmd :: Text -> Text -> Text
dropSimpleCmd tag t =
  let pat = "\\" <> T.takeWhile (/='{') (T.drop 1 tag) <> tag
  in T.replace pat "" t

stripBraces :: Text -> Text
stripBraces = T.filter (\c -> c /= '{' && c /= '}')

cleanupDeps :: Text -> Text
cleanupDeps t =
  let u = T.filter (not . (`elem` ("[](){}" :: String))) (T.toLower t)
      v = T.strip u
  in if v `elem` ["", "none", "∅"] then "" else t

cleanupLine :: Text -> Text
cleanupLine = T.dropAround (\c -> isSpace c || c == '(' || c == ')')

-- Map LaTeX/ASCII tokens to Unicode; run twice to catch leftovers.
normalizeLogic :: Text -> Text
normalizeLogic = pass . pass . T.unwords . T.words
  where
    pass = multi
      [ ("\\leftrightarrow", "↔"), ("\\Leftrightarrow", "↔")
      , ("\\iff", "↔"), ("<->", "↔"), ("<=>", "↔"), ("↔", "↔")

      , ("\\rightarrow", "→"), ("\\Rightarrow", "→")
      , ("\\to", "→"), ("->", "→"), ("=>", "→"), ("→", "→")
      , (" rightarrow ", " → ") -- crude, helps when OCR makes it a word

      , ("\\vee", "∨"), ("\\lor", "∨"), (" v ", " ∨ "), ("∨", "∨"), ("vee", "∨")

      , ("\\wedge", "∧"), ("\\land", "∧"), (" & ", " ∧ "), ("∧", "∧"), ("wedge", "∧")

      , ("\\neg", "¬"), ("\\lnot", "¬"), ("¬", "¬"), ("~", "¬"), ("!", "¬"), (" not ", " ¬ ")
      ]

    multi reps t = foldl (\acc (a,b) -> T.replace a b acc) t reps

-- tiny maybe (so we don't import Data.Maybe)
mapMaybe :: (a -> Maybe b) -> [a] -> [b]
mapMaybe f = foldr (\x acc -> maybe acc (:acc) (f x)) []
