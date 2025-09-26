-- src/LatexPretty.hs
module LatexPretty
  ( ppTermLaTeX
  , ppFormulaLaTeX
  , ppFormulaLaTeX'
  , LaTeXStyle(..)
  , defaultStyle
  ) where

import           Data.List (intercalate)
import           ProofTypes

-- ──────────────────────────────────────────────────────────────
-- Style options
-- ──────────────────────────────────────────────────────────────

data LaTeXStyle = LaTeXStyle
  { showPredParens   :: Bool
  , constWrapper     :: String -> String
  , predWrapper      :: String -> String
  , varWrapper       :: String -> String
  }

defaultStyle :: LaTeXStyle
defaultStyle = LaTeXStyle
  { showPredParens = True
  , constWrapper   = escape
  , predWrapper    = escape
  , varWrapper     = escape
  }

-- ──────────────────────────────────────────────────────────────
-- Public interface
-- ──────────────────────────────────────────────────────────────

ppTermLaTeX :: Term -> String
ppTermLaTeX = ppT defaultStyle

ppFormulaLaTeX :: PredFormula -> String
ppFormulaLaTeX = ppFormulaLaTeX' defaultStyle

ppFormulaLaTeX' :: LaTeXStyle -> PredFormula -> String
ppFormulaLaTeX' st = goTop
  where
    -- binary connective detector
    isBinary :: PredFormula -> Bool
    isBinary And{}     = True
    isBinary Or{}      = True
    isBinary Implies{} = True
    isBinary _         = False

    -- wrapper: add parens only if φ is binary
    wrapIfBin :: PredFormula -> String
    wrapIfBin φ
      | isBinary φ = "(" ++ goTop φ ++ ")"
      | otherwise  = goTop φ

    wrapIfComplex :: PredFormula -> String
    wrapIfComplex φ
      | isBinary φ = "(" ++ goTop φ ++ ")"
      | Not{}      <- φ = "(" ++ goTop φ ++ ")"
      | otherwise       = goTop φ

    -- top-level printer (never adds outer parens)
    goTop (Boolean True)   = "\\top"
    goTop (Boolean False)  = "\\bot"

    goTop (Predicate name ts)
      | null ts   = predWrapper st name
      | otherwise =
          let args = intercalate ", " (map (ppT st) ts)
          in if showPredParens st
                then predWrapper st name ++ "(" ++ args ++ ")"
                else unwords (predWrapper st name : map (ppT st) ts)

    goTop (Not φ)          = "\\neg " ++ goTop φ

    goTop (And φ ψ)        = wrapIfBin φ ++ " \\wedge " ++ wrapIfBin ψ
    goTop (Or φ ψ)         = wrapIfBin φ ++ " \\vee "   ++ wrapIfBin ψ
    goTop (Implies φ ψ)    = wrapIfBin φ ++ " \\to "    ++ wrapIfBin ψ

    goTop (ForAll x φ)     = "\\forall " ++ varWrapper st x ++ " " ++ wrapIfComplex φ
    goTop (Exists x φ)     = "\\exists " ++ varWrapper st x ++ " " ++ wrapIfComplex φ

-- ──────────────────────────────────────────────────────────────
-- Term pretty printer
-- ──────────────────────────────────────────────────────────────

ppT :: LaTeXStyle -> Term -> String
ppT st (Var x)   = varWrapper st x
ppT st (Const c) = constWrapper st c

-- ──────────────────────────────────────────────────────────────
-- Helpers
-- ──────────────────────────────────────────────────────────────

escape :: String -> String
escape = concatMap go
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

