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

-- You can tweak these knobs if you want a different visual style later.
data LaTeXStyle = LaTeXStyle
  { showPredParens   :: Bool        -- R(x,y) vs. R x y   (we default to parentheses)
  , constWrapper     :: String -> String  -- how to render constants
  , predWrapper      :: String -> String  -- how to render predicate / function symbols
  , varWrapper       :: String -> String  -- how to render variables
  }

defaultStyle :: LaTeXStyle
defaultStyle = LaTeXStyle
  { showPredParens = True
  , constWrapper   = (\s -> "\\mathsf{" ++ escape s ++ "}")
  , predWrapper    = (\s -> "\\mathit{" ++ escape s ++ "}")
  , varWrapper     = (\s -> escape s)   -- math italics is default for variables
  }

-- Public: pretty-print a term/formula (math-mode content; you wrap with $ ... $ or \[ ... \])
ppTermLaTeX :: Term -> String
ppTermLaTeX = ppT defaultStyle

ppFormulaLaTeX :: PredFormula -> String
ppFormulaLaTeX = ppF defaultStyle 0

-- Variant with custom style
ppFormulaLaTeX' :: LaTeXStyle -> PredFormula -> String
ppFormulaLaTeX' st = ppF st 0

-- ──────────────────────────────────────────────────────────────────────────────
-- Internal: precedence-aware printer
-- Precedence order (higher number = binds tighter):
--   0 : top
--   1 : → (Implies)
--   2 : ∨
--   3 : ∧
--   4 : ¬ and quantifiers
--   5 : atoms
-- ──────────────────────────────────────────────────────────────────────────────

type Prec = Int
pTop, pImpl, pOr, pAnd, pNot, pAtom :: Prec
pTop = 0; pImpl = 1; pOr = 2; pAnd = 3; pNot = 4; pAtom = 5

ppF :: LaTeXStyle -> Prec -> PredFormula -> String
ppF st _   (Boolean True)  = "\\top"
ppF st _   (Boolean False) = "\\bot"

ppF st _   (Predicate name []) =
  -- 0-ary predicate: treat like a propositional constant symbol
  predWrapper st name
ppF st _   (Predicate name ts) =
  let headTxt = predWrapper st name
      args    = intercalate ", " (map (ppT st) ts)
  in if showPredParens st
        then headTxt ++ "(" ++ args ++ ")"
        else unwords (headTxt : map (ppT st) ts)

ppF st ctx (Not φ) =
  wrap ctx pNot $ "\\lnot " ++ ppF st pNot φ

ppF st ctx (And φ ψ) =
  wrap ctx pAnd $ ppF st pAnd φ ++ " \\land " ++ ppF st pAnd ψ

ppF st ctx (Or  φ ψ) =
  wrap ctx pOr  $ ppF st pOr  φ ++ " \\lor "  ++ ppF st pOr  ψ

ppF st ctx (Implies φ ψ) =
  wrap ctx pImpl $ ppF st (pImpl+1) φ ++ " \\to " ++ ppF st pImpl ψ
  -- (pImpl+1) on left keeps A→B→C printing as A → (B → C)

ppF st ctx (ForAll x φ) =
  wrap ctx pNot $ "\\forall " ++ varWrapper st x ++ "\\, " ++ ppF st pNot φ

ppF st ctx (Exists x φ) =
  wrap ctx pNot $ "\\exists " ++ varWrapper st x ++ "\\, " ++ ppF st pNot φ

-- Terms (adjust if you later reintroduce function symbols)
ppT :: LaTeXStyle -> Term -> String
ppT st (Var x)   = varWrapper st x
ppT st (Const c) = constWrapper st c
-- If you do add function symbols back (e.g. Func f [t1..tn]), use:
-- ppT st (Func f ts) =
--   let headTxt = predWrapper st f
--       args    = intercalate ", " (map (ppT st) ts)
--   in if null ts then headTxt else headTxt ++ "(" ++ args ++ ")"

-- Parenthesize when the child has lower precedence than context.
wrap :: Prec -> Prec -> String -> String
wrap ctx me s = if me < ctx then "(" ++ s ++ ")" else s

-- Minimal LaTeX escaper for identifiers used in math mode.
escape :: String -> String
escape = concatMap go
  where
    go '_' = "\\_"
    go '#' = "\\#"
    go '&' = "\\&"
    go '%' = "\\%"
    go '$' = "\\$"
    go '{' = "\\{"
    go '}' = "\\}"
    go '^' = "\\^{}"
    go '~' = "\\~{}"
    go '\\' = "\\textbackslash{}"
    go c   = [c]
