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

data PredArgStyle = Parens | Spaced | Adjacent

data LaTeXStyle = LaTeXStyle
  { predArgStyle    :: PredArgStyle              -- changed
  , constWrapper    :: String -> String
  , predWrapper     :: String -> String
  , varWrapper      :: String -> String
  }

defaultStyle :: LaTeXStyle
defaultStyle = LaTeXStyle
  { predArgStyle  = Adjacent   -- default to classical
  , constWrapper  = escape
  , predWrapper   = escape
  , varWrapper    = escape
  }  

ppTermLaTeX :: Term -> String
ppTermLaTeX = ppT defaultStyle

ppFormulaLaTeX :: PredFormula -> String
ppFormulaLaTeX = ppFormulaLaTeX' defaultStyle

ppFormulaLaTeX' :: LaTeXStyle -> PredFormula -> String
ppFormulaLaTeX' st = ppF st

ppF :: LaTeXStyle -> PredFormula -> String
ppF st (Boolean True)  = "\\top"
ppF st (Boolean False) = "\\bot"

-- ✅ SPECIAL CASE for equality (infix)
ppF st (Predicate "=" [t1, t2]) = ppT st t1 ++ " = " ++ ppT st t2

ppF st (Predicate name []) = predWrapper st name
ppF st (Predicate name ts) =
  let headTxt = predWrapper st name
      argsParens = intercalate ", " (map (ppT st) ts)
      argsAdj    = concatMap (ppT st) ts
  in case predArgStyle st of
       Parens     -> headTxt ++ "(" ++ argsParens ++ ")"
       Spaced     -> unwords (headTxt : map (ppT st) ts)
       Adjacent   -> headTxt ++ argsAdj

ppF st (Not φ)
  | isBinary φ = "\\neg (" ++ ppF st φ ++ ")"
  | otherwise  = "\\neg "  ++ ppF st φ

ppF st (And φ ψ)     = wrapIfBin st φ ++ " \\wedge " ++ wrapIfBin st ψ
ppF st (Or φ ψ)      = wrapIfBin st φ ++ " \\vee "   ++ wrapIfBin st ψ
ppF st (Implies φ ψ) = wrapIfBin st φ ++ " \\to "    ++ wrapIfBin st ψ

ppF st (ForAll x φ) =
  "\\forall " ++ varWrapper st x ++ " " ++ wrapIfQuant st φ

ppF st (Exists x φ) =
  "\\exists " ++ varWrapper st x ++ " " ++ wrapIfQuant st φ

-- ──────────────────────────────────────────────────────────────────────────────
-- Terms
-- ──────────────────────────────────────────────────────────────────────────────

ppT :: LaTeXStyle -> Term -> String
ppT st (Var x)   = varWrapper st x
ppT st (Const c) = constWrapper st c

-- ──────────────────────────────────────────────────────────────────────────────
-- Helpers
-- ──────────────────────────────────────────────────────────────────────────────

isBinary :: PredFormula -> Bool
isBinary And{}     = True
isBinary Or{}      = True
isBinary Implies{} = True
isBinary _         = False

wrapIfBin :: LaTeXStyle -> PredFormula -> String
wrapIfBin st φ
  | isBinary φ = "(" ++ ppF st φ ++ ")"
  | otherwise  = ppF st φ

wrapIfQuant :: LaTeXStyle -> PredFormula -> String
wrapIfQuant st φ
  | isBinary φ   = "(" ++ ppF st φ ++ ")"
  | otherwise    = ppF st φ

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
