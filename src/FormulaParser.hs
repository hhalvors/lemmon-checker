{-# LANGUAGE LambdaCase #-}

module FormulaParser
  ( parseFormula
  , runParser
  ) where

import           ProofTypes
import           Text.Parsec.String (Parser)
import qualified Text.Parsec as P
import           Text.Parsec
  ( try, eof, parse, spaces, char, string, satisfy
  , chainl1, chainr1, sepBy1, many1, oneOf
  )
import           Data.Char (isLower, isUpper)
import qualified Data.Set  as Set
import           Data.Set  (Set)

-- ----- Lexer helpers -----
lexeme :: Parser a -> Parser a
lexeme p = p <* spaces

symbol :: String -> Parser String
symbol = lexeme . string

parens :: Parser a -> Parser a
parens p = lexeme (char '(') *> p <* lexeme (char ')')

-- unicode operators
opNot, opAnd, opOr, opImp, opIff, opFA, opEX :: String
opNot = "¬"; opAnd = "∧"; opOr = "∨"; opImp = "→"; opIff = "↔"; opFA = "∀"; opEX = "∃"

-- identifiers
lowerIdent :: Parser String
lowerIdent = lexeme $ (:[]) <$> satisfy isLower

upperIdent :: Parser String
upperIdent = lexeme $ (:[]) <$> satisfy isUpper

-- entry points ------------------------------------------------------

parseFormula :: String -> Either String PredFormula
parseFormula s =
  case parse (spaces *> pIff Set.empty <* eof) "<input>" s of
    Left e  -> Left (show e)
    Right f -> Right f

runParser :: String -> Either String PredFormula
runParser = parseFormula

-- precedence: ¬/quantifiers > ∧,∨ (left) > → (right) ----------------

op :: String -> (PredFormula -> PredFormula -> PredFormula)
   -> Parser (PredFormula -> PredFormula -> PredFormula)
op s c = symbol s *> pure c

-- NEW: top-level biconditional parser
pIff :: Set String -> Parser PredFormula
pIff env = chainr1 (pImp env) (op opIff Iff)

pImp :: Set String -> Parser PredFormula
pImp env = chainr1 (pAndOr env) (op opImp Implies)

pAndOr :: Set String -> Parser PredFormula
pAndOr env = chainl1 (pUnary env) ( (op opAnd And) P.<|> (op opOr Or) )

pUnary :: Set String -> Parser PredFormula
pUnary env =
      try (pQuant env)
  P.<|> (Not <$> (symbol opNot *> pUnary env))
  P.<|> pAtom env
  P.<|> parens (pIff env)

-- quantifiers -------------------------------------------------------

pQuant :: Set String -> Parser PredFormula
pQuant env = do
  q <- oneOf "∀∃AE"
  x <- satisfy isLower
  let constructor = if q `elem` "∀A" then ForAll else Exists
  body <- pUnary (Set.insert [x] env)
  return (constructor [x] body)

-- terms -------------------------------------------------------------

term :: Set String -> Parser Term
term env = do
  x <- lowerIdent
  pure $ if x `Set.member` env then Var x else Const x

termListParens :: Set String -> Parser [Term]
termListParens env = parens $ term env `sepBy1` lexeme (char ',')

termListBare :: Set String -> Parser [Term]
termListBare env = many1 (term env)

-- atoms: P, P(x,y), or bare-args Pxy -------------------------------

pEquality :: Set String -> Parser PredFormula
pEquality env = try $ do
  t1 <- term env
  _  <- symbol "="
  t2 <- term env
  return (Predicate "=" [t1, t2])

pAtom :: Set String -> Parser PredFormula
pAtom env =
      try (pEquality env)
  P.<|> try withParens
  P.<|> try bareArgs
  P.<|> noArgs
  where
    withParens = do
      predName <- upperIdent
      args <- termListParens env
      pure (Predicate predName args)

    bareArgs = do
      predName <- upperIdent
      args <- many1 (term env)
      pure (Predicate predName args)

    noArgs = do
      predName <- upperIdent
      pure (Predicate predName [])

