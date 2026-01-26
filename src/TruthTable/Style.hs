module TruthTable.Style
  ( TruthStyle(..)
  , truthText        -- for Text + HTML display glyphs
  , truthLaTeX       -- for LaTeX glyphs
  ) where

data TruthStyle
  = StyleTF       -- T/F
  | StyleBits     -- 1/0
  | StyleTopBot   -- ⊤/⊥  (LaTeX uses \top/\bot)
  deriving (Eq, Show, Read)

truthText :: TruthStyle -> Bool -> String
truthText st b =
  case st of
    StyleTF     -> if b then "T" else "F"
    StyleBits   -> if b then "1" else "0"
    StyleTopBot -> if b then "⊤" else "⊥"

truthLaTeX :: TruthStyle -> Bool -> String
truthLaTeX st b =
  case st of
    StyleTF     -> if b then "T" else "F"
    StyleBits   -> if b then "1" else "0"
    StyleTopBot -> if b then "\\top" else "\\bot"

