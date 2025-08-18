module Main where

import ProofTypes
import FormulaParser (parseFormula)
import ModelSemantics
import qualified Data.Set as S
import qualified Data.Map.Strict as M

m :: Model
m = Model
      { domain      = S.fromList ["a","b"]
      , constInterp = M.fromList [("a","a")]
      , predInterp  = M.fromList [(("P",1), fromTuples [["a"]])]
      }

main :: IO ()
main = do
  let Right φ = parseFormula "∀x(Px ∨ ¬Px)"
      Right ψ = parseFormula "P(a)"
  print (evalClosed m φ)  -- should be Right True
  print (evalClosed m ψ)  -- should be Right True
