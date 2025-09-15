-- src/ProofToLatex.hs
module ProofToLaTeX
  ( TableOrder(..)
  , RenderOpts(..)
  , defaultRenderOpts
  , proofTableLaTeX       -- ^ fragment: just the \begin{tabular} ... \end{tabular}
  , proofDocumentLaTeX    -- ^ full LaTeX document using the table
  ) where

import Data.List (intercalate, sort)
import qualified Data.Set as S
import ProofTypes
import LatexPretty (ppFormulaLaTeX)
import Data.List (sortBy)
import Data.Ord  (comparing)

-- ── Column ordering — you asked earlier about swapping Line/Deps.
data TableOrder = LineDeps | DepsLine
  deriving (Eq, Show)

data RenderOpts = RenderOpts
  { order        :: TableOrder
  , header       :: Bool         -- show a header row
  , mathDelims   :: (String,String) -- e.g. ("$", "$") or ("\\(", "\\)")
  }

defaultRenderOpts :: RenderOpts
defaultRenderOpts = RenderOpts
  { order      = DepsLine
  , header     = True
  , mathDelims = ("$", "$")
  }

-- Public: make just the table
proofTableLaTeX :: RenderOpts -> [ProofLine] -> String
proofTableLaTeX opts ls =
  let colSpec = ">{\\raggedleft\\arraybackslash}p{1.5cm}\
                \ >{\\centering\\arraybackslash}p{1.0cm}\
                \ p{5cm}\
                \ >{\\raggedright\\arraybackslash}p{3.5cm}"

      rows     = map (renderLine opts) (sortOnLine ls)

      -- Make the header row, and ensure it ends with \\ \hline
      hdrRow   = case header opts of
                   True  -> headerRow (order opts) ++ " \\\\ \\hline"
                   False -> ""   -- no header text, but we’ll still draw the top \hline
  in unlines $
       [ "\\begin{tabular}{" ++ colSpec ++ "}"
       , "\\hline"
       , hdrRow
       ]
       -- each row just ends with \\ (no \hline between or after)
       ++ map (++ " \\\\") rows
       ++ [ "\\end{tabular}" ]  


-- Public: wrap table in a minimal, compilable LaTeX document
proofDocumentLaTeX :: String -> RenderOpts -> [ProofLine] -> String
proofDocumentLaTeX title opts ls =
  unlines
    [ "\\documentclass[12pt]{article}"
    , "\\usepackage[margin=1in]{geometry}"
    , "\\usepackage{amsmath,amssymb}"
    , "\\usepackage{array}"
    , "\\usepackage[T1]{fontenc}"
    , "\\usepackage{lmodern}"
    , "\\begin{document}"
    , "\\section*{" ++ escapeText title ++ "}"
    , proofTableLaTeX opts ls
    , "\\end{document}"
    ]

-- ──────────────────────────────────────────────────────────────────────────────
-- Rendering
-- ──────────────────────────────────────────────────────────────────────────────

renderLine :: RenderOpts -> ProofLine -> String
renderLine opts pl =
  let (ld, rd)   = mathDelims opts
      lnTxt      = "(" ++ show (lineNumber pl) ++ ")"
      depsTxt    = ppRefs (references pl)
      formulaTxt = ld ++ ppFormulaLaTeX (formula pl) ++ rd
      justTxt    = ppJust (justification pl)
  in case order opts of
       LineDeps -> joinCols [lnTxt, depsTxt, formulaTxt, justTxt]
       DepsLine -> joinCols [depsTxt, lnTxt, formulaTxt, justTxt]

headerRow :: TableOrder -> String
headerRow LineDeps = "\\textbf{Line} & \\textbf{Deps} & \\textbf{Formula} & \\textbf{Justification} \\\\ \\hline"
headerRow DepsLine = "\\textbf{Deps} & \\textbf{Line} & \\textbf{Formula} & \\textbf{Justification} \\\\ \\hline"

joinCols :: [String] -> String
joinCols = intercalate " & "

ppRefs :: S.Set Int -> String
ppRefs s =
  case sort (S.toList s) of
    []  -> "$\\varnothing$"           -- nice touch for empty set
    xs  -> intercalate "," (map show xs)

-- numbers-first, short-tag justification
ppJust :: Justification -> String
ppJust Assumption = "A"
ppJust j =
  let tag :: String
      tag = case j of
        MP _ _               -> "MP"
        MT _ _               -> "MT"
        DN _                 -> "DN"
        CP _ _               -> "CP"
        AndIntro _ _         -> "∧I"
        AndElim _            -> "∧E"
        OrIntro _            -> "∨I"
        OrElim _ _ _ _ _     -> "∨E"
        RAA _ _              -> "RAA"
        ForallElim _         -> "∀E"
        ForallIntro _        -> "∀I"
        ExistsIntro _        -> "∃I"
        ExistsElim _ _ _     -> "∃E"
        Assumption           -> "A"  -- already handled

      nums :: [Int]
      nums = case j of
        MP m n               -> [m,n]
        MT m n               -> [m,n]
        DN m                 -> [m]
        CP m n               -> [m,n]
        AndIntro m n         -> [m,n]
        AndElim m            -> [m]
        OrIntro m            -> [m]
        OrElim d a p b c     -> [d,a,p,b,c]
        RAA a c              -> [a,c]
        ForallElim m         -> [m]
        ForallIntro m        -> [m]
        ExistsIntro m        -> [m]
        ExistsElim m a n     -> [m,a,n]
        Assumption           -> []

      numsTxt = intercalate "," (map show nums)
  in if null nums then tag else numsTxt ++ " " ++ tag


-- Sort by line number just in case the caller gives us unsorted lines
sortOnLine :: [ProofLine] -> [ProofLine]
sortOnLine = sortBy (comparing lineNumber)

-- Escape only text used outside math (table headers, title)
escapeText :: String -> String
escapeText = concatMap go
  where
    go '#' = "\\#"; go '$' = "\\$"; go '%' = "\\%"; go '&' = "\\&"
    go '_' = "\\_"; go '{' = "\\{"; go '}' = "\\}"; go '^' = "\\^{}"
    go '~' = "\\~{}"; go '\\' = "\\textbackslash{}"
    go c   = [c]
