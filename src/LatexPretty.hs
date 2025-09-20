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

-- ──────────────────────────────────────────────────────────────────────────────
-- Style options
-- ──────────────────────────────────────────────────────────────────────────────

data LaTeXStyle = LaTeXStyle
  { showPredParens   :: Bool               -- R(x,y) vs. R x y
  , constWrapper     :: String -> String   -- render constants
  , predWrapper      :: String -> String   -- render predicate/function names
  , varWrapper       :: String -> String   -- render variables
  }

defaultStyle :: LaTeXStyle
defaultStyle = LaTeXStyle
  { showPredParens = True
  , constWrapper   = \s -> "\\mathsf{" ++ escape s ++ "}"
  , predWrapper    = \s -> "\\mathit{" ++ escape s ++ "}"
  , varWrapper     = \s -> escape s
  }

-- ──────────────────────────────────────────────────────────────────────────────
-- Public interface
-- ──────────────────────────────────────────────────────────────────────────────

ppTermLaTeX :: Term -> String
ppTermLaTeX = ppT defaultStyle

ppFormulaLaTeX :: PredFormula -> String
ppFormulaLaTeX = ppFormulaLaTeX' defaultStyle

ppFormulaLaTeX' :: LaTeXStyle -> PredFormula -> String
ppFormulaLaTeX' st f@(Not _) = ppF st f
ppFormulaLaTeX' st f@(Boolean _) = ppF st f
ppFormulaLaTeX' st f@(Predicate _ _) = ppF st f
ppFormulaLaTeX' st f = stripOuterParens (ppF st f)

-- ──────────────────────────────────────────────────────────────────────────────
-- Formula pretty printer
-- ──────────────────────────────────────────────────────────────────────────────

ppF :: LaTeXStyle -> PredFormula -> String
ppF st (Boolean True)  = "\\top"
ppF st (Boolean False) = "\\bot"

ppF st (Predicate name []) = predWrapper st name
ppF st (Predicate name ts) =
  let headTxt = predWrapper st name
      args    = intercalate ", " (map (ppT st) ts)
  in if showPredParens st
        then headTxt ++ "(" ++ args ++ ")"
        else unwords (headTxt : map (ppT st) ts)

-- Negation: avoid extra parens unless operand is complex
ppF st (Not f@(Predicate _ _)) = "\\neg " ++ ppF st f
ppF st (Not f@(Boolean _))     = "\\neg " ++ ppF st f
ppF st (Not f@(Not _))         = "\\neg " ++ ppF st f
ppF st (Not f)                 = "\\neg (" ++ ppF st f ++ ")"

-- Fully parenthesize binary connectives
ppF st (And φ ψ) = "(" ++ ppF st φ ++ " \\wedge " ++ ppF st ψ ++ ")"
ppF st (Or  φ ψ) = "(" ++ ppF st φ ++ " \\vee "   ++ ppF st ψ ++ ")"
ppF st (Implies φ ψ) = "(" ++ ppF st φ ++ " \\to " ++ ppF st ψ ++ ")"

-- Quantifiers
ppF st (ForAll x φ) =
  "\\forall " ++ varWrapper st x ++ "\\, " ++ wrapIfComplex (ppF st φ)

ppF st (Exists x φ) =
  "\\exists " ++ varWrapper st x ++ "\\, " ++ wrapIfComplex (ppF st φ)

-- ──────────────────────────────────────────────────────────────────────────────
-- Term pretty printer
-- ──────────────────────────────────────────────────────────────────────────────

ppT :: LaTeXStyle -> Term -> String
ppT st (Var x)   = varWrapper st x
ppT st (Const c) = constWrapper st c

-- ──────────────────────────────────────────────────────────────────────────────
-- Helpers
-- ──────────────────────────────────────────────────────────────────────────────

wrapIfComplex :: String -> String
wrapIfComplex s =
  if isAtomic s then s else "(" ++ s ++ ")"

isAtomic :: String -> Bool
isAtomic s = all (`notElem` s) ("\\() " :: String)

stripOuterParens :: String -> String
stripOuterParens s =
  case s of
    '(' : rest | last s == ')' -> init rest
    _ -> s

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

