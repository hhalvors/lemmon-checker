-- src/Normalize.hs
module Normalize (normalizeSyntax) where

import Data.Char (toLower, isSpace, isAlphaNum)

normalizeSyntax :: String -> String
normalizeSyntax =
      repl "\\/"  "∨"
    . repl "v"    "∨"  
    . repl "/\\"  "∧"
    . repl "&"    "∧"
    . repl "->"   "→"
    . repl "=>"   "→"
    . repl "~"    "¬"
    -- English words (case-insensitive, word boundaries)
    . replWordCI "not" "¬"
    . replWordCI "and" "∧"
    . replWordCI "or"  "∨"
    -- Quantifiers (long form)
    . replQuantCI "forall" '∀'
    . replQuantCI "exists" '∃'
    -- Quantifiers (short form: Ax, Ex)
    . replAxEx

-- -------------------------
-- Helpers
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
      , wordBoundary mprev
      , wordBoundary (nextChar s)
      = sub ++ go (Just (lastChar sub)) (drop lp s)
      | otherwise = c : go (Just c) cs

    wordBoundary Nothing   = True
    wordBoundary (Just ch) = not (isAlphaNum ch)

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

-- Handle Ax... and Ex... shorthand
replAxEx :: String -> String
replAxEx [] = []
replAxEx (a:x:rest)
  | (a == 'A' || a == 'a') && isVarChar x = '∀' : x : replAxEx rest
  | (a == 'E' || a == 'e') && isVarChar x = '∃' : x : replAxEx rest
replAxEx (c:cs) = c : replAxEx cs

isVarChar :: Char -> Bool
isVarChar c = isAlphaNum c

-- simple prefix check
isPrefixOf :: String -> String -> Bool
isPrefixOf a b = take (length a) b == a
