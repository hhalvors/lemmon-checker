-- src/FormulaParser.hs
{-# LANGUAGE LambdaCase #-}

module FormulaParser
  ( parseFormula           -- String -> Either String PredFormula
  , runParser              -- alias
  ) where

import           ProofTypes
import           Text.Parsec.String (Parser)
import           Text.Parsec
  ( (<|>), try, eof, parse, spaces, char, string, satisfy
  , chainl1, chainr1, sepBy1, many1
  )
import           Data.Char (isLower, isUpper)
import qualified Data.Set  as Set
import           Data.Set  (Set)

-- ----- tiny lexer helpers -----
lexeme :: Parser a -> Parser a
lexeme p = p <* spaces

symbol :: String -> Parser String
symbol = lexeme . string

parens :: Parser a -> Parser a
parens p = lexeme (char '(') *> p <* lexeme (char ')')

-- unicode tokens
opNot, opAnd, opOr, opImp, opFA, opEX :: String
opNot = "¬"; opAnd = "∧"; opOr = "∨"; opImp = "→"; opFA = "∀"; opEX = "∃"

-- identifiers (single letters for now)
lowerIdent :: Parser String
lowerIdent = lexeme $ (:[]) <$> satisfy isLower

upperIdent :: Parser String
upperIdent = lexeme $ (:[]) <$> satisfy isUpper

-- entry points ------------------------------------------------------

parseFormula :: String -> Either String PredFormula
parseFormula s = case parse (spaces *> pImp Set.empty <* eof) "<input>" s of
  Left e  -> Left (show e)
  Right f -> Right f

runParser :: String -> Either String PredFormula
runParser = parseFormula

-- precedence: ¬/quantifiers > ∧,∨ (left) > → (right) ----------------

op :: String -> (PredFormula -> PredFormula -> PredFormula)
   -> Parser (PredFormula -> PredFormula -> PredFormula)
op s c = symbol s *> pure c

pImp :: Set String -> Parser PredFormula
pImp env = chainr1 (pAndOr env) (op opImp Implies)

pAndOr :: Set String -> Parser PredFormula
pAndOr env = chainl1 (pUnary env) ((op opAnd And) <|> (op opOr Or))

pUnary :: Set String -> Parser PredFormula
pUnary env =
      pQuant env
  <|> (Not <$> (symbol opNot *> pUnary env))
  <|> pAtom env
  <|> parens (pImp env)

-- quantifiers extend the bound‑variable environment -----------------

pQuant :: Set String -> Parser PredFormula
pQuant env =
      do _ <- symbol opFA
         x <- lowerIdent
         ForAll x <$> pUnary (Set.insert x env)
  <|> do _ <- symbol opEX
         x <- lowerIdent
         Exists x <$> pUnary (Set.insert x env)

-- terms that respect the bound‑variable environment -----------------

term :: Set String -> Parser Term
term env = do
  x <- lowerIdent
  pure $ if x `Set.member` env then Var x else Const x

termListParens :: Set String -> Parser [Term]
termListParens env = parens $ term env `sepBy1` lexeme (char ',')

termListBare :: Set String -> Parser [Term]
termListBare env = many1 (term env)

-- atoms: P, P(x,y), or bare-args Pxy --------------------------------

pAtom :: Set String -> Parser PredFormula
pAtom env = do
  predName <- upperIdent
  args <-   try (termListParens env)
        <|> try (termListBare   env)
        <|> pure []
  pure (Predicate predName args)
