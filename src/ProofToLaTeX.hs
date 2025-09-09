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
  let colSpec = ">{\\raggedleft\\arraybackslash}p{1.0cm}\
                \ >{\\raggedright\\arraybackslash}p{1.6cm}\
                \ p{9cm}\
                \ >{\\raggedright\\arraybackslash}p{3.5cm}"
      -- If you prefer exact widths, tweak the p{..} lengths above.
      rows     = map (renderLine opts) (sortOnLine ls)
      hdr      = if header opts then headerRow (order opts) else ""
  in unlines $
       [ "\\begin{tabular}{" ++ colSpec ++ "}"
       , "\\hline"
       , hdr
       ] ++ intercalate ["\\\\ \\hline"] (map (:[]) rows)
         ++ ["\\\\ \\hline", "\\end{tabular}"]

-- Public: wrap table in a minimal, compilable LaTeX document
proofDocumentLaTeX :: String -> RenderOpts -> [ProofLine] -> String
proofDocumentLaTeX title opts ls =
  unlines
    [ "\\documentclass[11pt]{article}"
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
      lnTxt      = show (lineNumber pl)
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

-- A compact, readable justification pretty-printer
ppJust :: Justification -> String
ppJust Assumption          = "Assumption"
ppJust (MP m n)            = "MP "  ++ show m ++ " " ++ show n
ppJust (MT m n)            = "MT "  ++ show m ++ " " ++ show n
ppJust (DN m)              = "DN "  ++ show m
ppJust (CP m n)            = "CP "  ++ show m ++ " " ++ show n
ppJust (AndIntro m n)      = "$\\land$ Intro " ++ show m ++ " " ++ show n
ppJust (AndElim m)         = "$\\land$ Elim "  ++ show m
ppJust (OrIntro m)         = "$\\lor$ Intro "  ++ show m
ppJust (OrElim d a p b c)  = "$\\lor$ Elim "   ++ unwords (map show [d,a,p,b,c])
ppJust (ForallElim m)      = "$\\forall$ Elim "  ++ show m
ppJust (ForallIntro m)     = "$\\forall$ Intro " ++ show m
ppJust (ExistsIntro m)     = "$\\exists$ Intro " ++ show m
ppJust (ExistsElim m a n)  = "$\\exists$ Elim "  ++ unwords (map show [m,a,n])

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
