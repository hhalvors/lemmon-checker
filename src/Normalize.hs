-- src/Normalize.hs
module Normalize
  ( normalizeSyntax        -- legacy, whole-text (avoid on /check)
  , normalizeFormula       -- NEW: normalize only a formula cell
  ) where

import Data.Char (toLower, isSpace, isAlphaNum)

-- =========================================================
-- Whole-text normalizer (legacy). Leave as-is for OCR etc.
-- =========================================================
normalizeSyntax :: String -> String
normalizeSyntax =
      repl "\\/"  "∨"
    . repl "v"    "∨"
    . repl "/\\"  "∧"
    . repl "&"    "∧"
    . repl "->"   "→"
    . repl "=>"   "→"
    . repl "~"    "¬"
    . replWordCI "not" "¬"
    . replWordCI "and" "∧"
    . replWordCI "or"  "∨"
    . replQuantCI "forall" '∀'
    . replQuantCI "exists" '∃'
    -- ⚠ Avoid Ax/Ex here, because it mangles rule names like RAA.
    -- . replAxEx    -- ← do NOT use globally

-- =========================================================
-- Formula-only normalizer (safe for the formula column)
-- =========================================================
normalizeFormula :: String -> String
normalizeFormula =
      repl "\\/"  "∨"
    . repl "v"    "∨"
    . repl "/\\"  "∧"
    . repl "&"    "∧"
    . repl "->"   "→"
    . repl "=>"   "→"
    . repl "~"    "¬"
    . replQuantCI "forall" '∀'
    . replQuantCI "exists" '∃'
    . replAxExBoundary   -- ✅ Ax… / Ex… only at a word boundary

-- -------------------------
-- Helpers (unchanged + new)
-- -------------------------

repl :: String -> String -> String -> String
repl pat sub = go
  where
    lp = length pat
    go s
      | pat `isPrefixOf` s = sub ++ go (drop lp s)
      | null s             = ""
      | otherwise          = head s : go (tail s)

replWordCI :: String -> String -> String -> String
replWordCI pat sub = go Nothing
  where
    lp = length pat
    lo = map toLower pat

    go _ [] = []
    go mprev s@(c:cs)
      | map toLower (take lp s) == lo
      , boundary mprev
      , boundary (nextChar s)
      = sub ++ go (Just (lastChar sub)) (drop lp s)
      | otherwise = c : go (Just c) cs

    boundary Nothing   = True
    boundary (Just ch) = not (isAlphaNum ch)

    nextChar str = case drop lp str of
                     (d:_) -> Just d
                     []    -> Nothing

    lastChar [] = ' '
    lastChar xs = last xs

replQuantCI :: String -> Char -> String -> String
replQuantCI pat q = go
  where
    lp = length pat
    lo = map toLower pat
    go [] = []
    go s
      | map toLower (take lp s) == lo =
          let rest0          = drop lp s
              (ws, restMore) = span isSpace rest0
          in q : ws ++ go restMore
      | otherwise = head s : go (tail s)

-- Boundary-aware Ax/Ex shorthand (won't touch "RAA", "EElim", etc.)
replAxExBoundary :: String -> String
replAxExBoundary = go Nothing
  where
    go _ [] = []
    go mprev (c1:c2:rest)
      | isBoundary mprev
      , c1 == 'A'
      , isVarChar c2
      = '∀' : c2 : go (Just c2) rest

      | isBoundary mprev
      , c1 == 'E'
      , isVarChar c2
      = '∃' : c2 : go (Just c2) rest

      | otherwise = c1 : go (Just c1) (c2:rest)
    go mprev [c] = [c]  -- tail case

    isBoundary Nothing   = True
    isBoundary (Just ch) = not (isAlphaNum ch)

isVarChar :: Char -> Bool
isVarChar = isAlphaNum

-- simple prefix check
isPrefixOf :: String -> String -> Bool
isPrefixOf a b = take (length a) b == a
