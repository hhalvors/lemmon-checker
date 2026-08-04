-- test/Tests.hs
--
-- Regression corpus for the proof checker.
--
-- Each case is a proof written in the pipe format the web front end accepts,
-- paired with what should happen to it. Writing them as source text rather
-- than as ProofLine values means every case exercises the whole path —
-- normaliser, formula parser, justification parser, checker — and keeps the
-- corpus readable enough to serve as documentation of what each rule requires.
--
-- The aim is one valid proof and two invalid variants per rule. The invalid
-- variants are chosen to be *nearly* right: they are mistakes a student
-- actually makes (conjuncts in the wrong order, dependencies not propagated,
-- a witness constant that is not arbitrary), not obvious nonsense. A checker
-- that only rejects nonsense is not much of a checker.
--
-- Run with: stack test

module Main where

import ProofTypes     (Proof)
import PipeParse      (parsePipeProof)
import LemmonChecker  (checkProof, proofValid, LineReport(..))
import Control.Monad  (forM_)
import Data.List      (intercalate)
import System.Exit    (exitFailure, exitSuccess)

--------------------------------------------------------------------------------
-- Expectations
--------------------------------------------------------------------------------

data Expect
  = Valid           -- ^ parses, and every line checks out
  | InvalidAt Int   -- ^ parses, and the checker faults (at least) this line
  | ParseFails      -- ^ the parser rejects it before the checker sees it

data Case = Case
  { caseName   :: String
  , caseText   :: String
  , caseExpect :: Expect
  }

-- | A proof, given as lines, so the corpus stays legible.
pf :: [String] -> String
pf = unlines

--------------------------------------------------------------------------------
-- The corpus
--------------------------------------------------------------------------------

suite :: [(String, [Case])]
suite =
  [ ( "Assumption"
    , [ Case "assumption depends on itself"
          (pf ["1|1|P|A"]) Valid
      , Case "assumption depending on the wrong line"
          (pf ["2|1|P|A"]) (InvalidAt 1)
      , Case "assumption with no dependencies"
          (pf ["|1|P|A"]) (InvalidAt 1)
      ] )

  , ( "MP"
    , [ Case "modus ponens"
          (pf [ "1|1|P→Q|A", "2|2|P|A", "1,2|3|Q|1,2 MP" ]) Valid
      , Case "concludes the antecedent instead of the consequent"
          (pf [ "1|1|P→Q|A", "2|2|P|A", "1,2|3|P|1,2 MP" ]) (InvalidAt 3)
      , Case "dependencies not pooled from both cited lines"
          (pf [ "1|1|P→Q|A", "2|2|P|A", "1|3|Q|1,2 MP" ]) (InvalidAt 3)
      ] )

  , ( "MT"
    , [ Case "modus tollens"
          (pf [ "1|1|P→Q|A", "2|2|¬Q|A", "1,2|3|¬P|1,2 MT" ]) Valid
      , Case "negates the consequent rather than the antecedent"
          (pf [ "1|1|P→Q|A", "2|2|¬Q|A", "1,2|3|¬Q|1,2 MT" ]) (InvalidAt 3)
      , Case "dependencies not pooled"
          (pf [ "1|1|P→Q|A", "2|2|¬Q|A", "2|3|¬P|1,2 MT" ]) (InvalidAt 3)
      -- The citation names the roles: conditional first, negated consequent
      -- second. Reasoning is fine here; the citation order is not.
      , Case "cited lines in the wrong order"
          (pf [ "1|1|¬Q|A", "2|2|P→Q|A", "1,2|3|¬P|1,2 MT" ]) (InvalidAt 3)
      ] )

  , ( "DN"
    , [ Case "double negation introduced"
          (pf [ "1|1|P|A", "1|2|¬¬P|1 DN" ]) Valid
      , Case "single negation is not double negation"
          (pf [ "1|1|P|A", "1|2|¬P|1 DN" ]) (InvalidAt 2)
      , Case "dependencies dropped"
          (pf [ "1|1|P|A", "|2|¬¬P|1 DN" ]) (InvalidAt 2)
      ] )

  , ( "CP"
    , [ Case "conditional proof discharges the assumption"
          (pf [ "1|1|P|A", "2|2|Q|A", "1,2|3|P∧Q|1,2 ∧I"
              , "1|4|Q→(P∧Q)|2,3 CP" ]) Valid
      , Case "antecedent and consequent the wrong way round"
          (pf [ "1|1|P|A", "2|2|Q|A", "1,2|3|P∧Q|1,2 ∧I"
              , "1|4|(P∧Q)→Q|2,3 CP" ]) (InvalidAt 4)
      , Case "discharged assumption still listed as a dependency"
          (pf [ "1|1|P|A", "2|2|Q|A", "1,2|3|P∧Q|1,2 ∧I"
              , "1,2|4|Q→(P∧Q)|2,3 CP" ]) (InvalidAt 4)
      ] )

  , ( "AndIntro"
    , [ Case "conjunction introduced"
          (pf [ "1|1|P|A", "2|2|Q|A", "1,2|3|P∧Q|1,2 ∧I" ]) Valid
      -- ∧I is order-insensitive: citing 1,2 licenses P∧Q and Q∧P alike.
      , Case "conjuncts in the opposite order from the citation"
          (pf [ "1|1|P|A", "2|2|Q|A", "1,2|3|Q∧P|1,2 ∧I" ]) Valid
      , Case "dependencies not pooled"
          (pf [ "1|1|P|A", "2|2|Q|A", "1|3|P∧Q|1,2 ∧I" ]) (InvalidAt 3)
      -- REGRESSION: the ∧I soundness hole. Until AndIntro was implemented,
      -- checkLine's catch-all accepted any formula on this line.
      , Case "conjunction unrelated to the cited lines"
          (pf [ "1|1|P|A", "2|2|Q|A", "1,2|3|P∧R|1,2 ∧I" ]) (InvalidAt 3)
      ] )

  , ( "AndElim"
    , [ Case "conjunct extracted"
          (pf [ "1|1|P∧Q|A", "1|2|P|1 ∧E" ]) Valid
      , Case "formula that is not one of the conjuncts"
          (pf [ "1|1|P∧Q|A", "1|2|R|1 ∧E" ]) (InvalidAt 2)
      , Case "dependencies dropped"
          (pf [ "1|1|P∧Q|A", "|2|P|1 ∧E" ]) (InvalidAt 2)
      ] )

  , ( "OrIntro"
    , [ Case "disjunction introduced"
          (pf [ "1|1|P|A", "1|2|P∨Q|1 ∨I" ]) Valid
      , Case "cited formula is not a disjunct of the goal"
          (pf [ "1|1|P|A", "1|2|Q∨R|1 ∨I" ]) (InvalidAt 2)
      , Case "goal is not a disjunction at all"
          (pf [ "1|1|P|A", "1|2|P∧Q|1 ∨I" ]) (InvalidAt 2)
      ] )

  , ( "OrElim"
    , [ Case "proof by cases"
          (pf [ "1|1|P∨Q|A", "2|2|P|A", "2|3|Q∨P|2 ∨I"
              , "4|4|Q|A", "4|5|Q∨P|4 ∨I"
              , "1|6|Q∨P|1,2,3,4,5 ∨E" ]) Valid
      , Case "the two cases do not reach the stated conclusion"
          (pf [ "1|1|P∨Q|A", "2|2|P|A", "2|3|Q∨P|2 ∨I"
              , "4|4|Q|A", "4|5|Q∨P|4 ∨I"
              , "1|6|P∨Q|1,2,3,4,5 ∨E" ]) (InvalidAt 6)
      , Case "case assumptions not discharged"
          (pf [ "1|1|P∨Q|A", "2|2|P|A", "2|3|Q∨P|2 ∨I"
              , "4|4|Q|A", "4|5|Q∨P|4 ∨I"
              , "1,2|6|Q∨P|1,2,3,4,5 ∨E" ]) (InvalidAt 6)
      ] )

  , ( "RAA"
    , [ Case "reductio discharges the assumption it refutes"
          (pf [ "1|1|P|A", "2|2|¬P|A", "1,2|3|P∧¬P|1,2 ∧I"
              , "2|4|¬P|1,3 RAA" ]) Valid
      , Case "concludes the assumption rather than its negation"
          (pf [ "1|1|P|A", "2|2|¬P|A", "1,2|3|P∧¬P|1,2 ∧I"
              , "2|4|P|1,3 RAA" ]) (InvalidAt 4)
      , Case "cited line is not a contradiction"
          (pf [ "1|1|P|A", "1|2|¬P|1,1 RAA" ]) (InvalidAt 2)
      ] )

  , ( "ForallElim"
    , [ Case "universal instantiated to a constant"
          (pf [ "1|1|∀xFx|A", "1|2|Fa|1 ∀E" ]) Valid
      , Case "cited line is not universally quantified"
          (pf [ "1|1|Fa|A", "1|2|Fb|1 ∀E" ]) (InvalidAt 2)
      , Case "dependencies dropped"
          (pf [ "1|1|∀xFx|A", "|2|Fa|1 ∀E" ]) (InvalidAt 2)
      ] )

  , ( "ExistsIntro"
    , [ Case "existential generalisation"
          (pf [ "1|1|Fa|A", "1|2|∃xFx|1 ∃I" ]) Valid
      , Case "goal is not existentially quantified"
          (pf [ "1|1|Fa|A", "1|2|Fa|1 ∃I" ]) (InvalidAt 2)
      , Case "cited line is not an instance of the goal body"
          (pf [ "1|1|Fa|A", "1|2|∃x(Fx∧Gx)|1 ∃I" ]) (InvalidAt 2)
      ] )

  , ( "ForallIntro"
    , [ Case "generalising on an arbitrary constant"
          (pf [ "1|1|P→∀xFx|A", "2|2|P|A", "1,2|3|∀xFx|1,2 MP"
              , "1,2|4|Fa|3 ∀E", "1|5|P→Fa|2,4 CP"
              , "1|6|∀x(P→Fx)|5 ∀I" ]) Valid
      , Case "constant is not arbitrary: it occurs in a live assumption"
          (pf [ "1|1|Fa|A", "1|2|∀xFx|1 ∀I" ]) (InvalidAt 2)
      -- Caught by the justification parser, which needs a ∀ goal to infer the
      -- variable, so it never reaches the checker by this route. The checker's
      -- own "not a universal sentence" guard still matters: `lemmon-check`
      -- reads Proof JSON directly and bypasses PipeParse entirely.
      , Case "goal is not a universal sentence"
          (pf [ "1|1|Fa|A", "1|2|Fa|1 ∀I" ]) ParseFails
      ] )

  , ( "ExistsElim"
    , [ Case "existential elimination with a fresh witness"
          (pf [ "1|1|∃xFx|A", "2|2|Fa|A", "2|3|∃xFx|2 ∃I"
              , "1|4|∃xFx|1,2,3 ∃E" ]) Valid
      , Case "witness constant escapes into the conclusion"
          (pf [ "1|1|∃xFx|A", "2|2|Fa|A", "2|3|Fa∨Ga|2 ∨I"
              , "1|4|Fa∨Ga|1,2,3 ∃E" ]) (InvalidAt 4)
      , Case "temporary assumption not discharged"
          (pf [ "1|1|∃xFx|A", "2|2|Fa|A", "2|3|∃xFx|2 ∃I"
              , "1,2|4|∃xFx|1,2,3 ∃E" ]) (InvalidAt 4)
      ] )

  , ( "EqIntro"
    , [ Case "self-identity"
          (pf [ "|1|a=a|=I" ]) Valid
      , Case "identity between distinct constants"
          (pf [ "|1|a=b|=I" ]) (InvalidAt 1)
      , Case "self-identity must not depend on anything"
          (pf [ "1|1|a=a|=I" ]) (InvalidAt 1)
      ] )

  , ( "EqElim"
    , [ Case "substituting b for a given a=b"
          (pf [ "1|1|Fa|A", "2|2|a=b|A", "1,2|3|Fb|1,2 =E" ]) Valid
      -- Documents current behaviour: =E replaces a by b, not b by a.
      , Case "substituting in the reverse direction"
          (pf [ "1|1|Fb|A", "2|2|a=b|A", "1,2|3|Fa|1,2 =E" ]) (InvalidAt 3)
      , Case "second cited line is not an identity"
          (pf [ "1|1|Fa|A", "2|2|P|A", "1,2|3|Fb|1,2 =E" ]) (InvalidAt 3)
      ] )

  , ( "LEM"
    , [ Case "excluded middle"
          (pf [ "|1|P∨¬P|LEM" ]) Valid
      , Case "disjuncts are not complementary"
          (pf [ "|1|P∨¬Q|LEM" ]) (InvalidAt 1)
      , Case "conjunction rather than disjunction"
          (pf [ "|1|P∧¬P|LEM" ]) (InvalidAt 1)
      ] )

  , ( "PropTaut"
    , [ Case "tautology with no premises"
          (pf [ "|1|P→P|prop taut" ]) Valid
      , Case "propositional consequence of a cited line"
          (pf [ "1|1|P|A", "1|2|P∨Q|1 prop taut" ]) Valid
      , Case "not a tautology on its own"
          (pf [ "|1|P∨Q|prop taut" ]) (InvalidAt 1)
      , Case "dependencies not inherited from the cited line"
          (pf [ "1|1|P|A", "|2|P∨Q|1 prop taut" ]) (InvalidAt 2)
      ] )

  , ( "IffIntro"
    , [ Case "biconditional from both conditionals"
          (pf [ "1|1|P→Q|A", "2|2|Q→P|A", "1,2|3|P↔Q|1,2 ↔I" ]) Valid
      , Case "same direction cited twice"
          (pf [ "1|1|P→Q|A", "2|2|P→Q|A", "1,2|3|P↔Q|1,2 ↔I" ]) (InvalidAt 3)
      , Case "dependencies not pooled"
          (pf [ "1|1|P→Q|A", "2|2|Q→P|A", "1|3|P↔Q|1,2 ↔I" ]) (InvalidAt 3)
      ] )

  , ( "IffElim"
    , [ Case "detaching one side of a biconditional"
          (pf [ "1|1|P↔Q|A", "2|2|P|A", "1,2|3|Q|1,2 ↔E" ]) Valid
      , Case "concluding something that is not the other side"
          (pf [ "1|1|P↔Q|A", "2|2|P|A", "1,2|3|R|1,2 ↔E" ]) (InvalidAt 3)
      , Case "cited formula is neither side of the biconditional"
          (pf [ "1|1|P↔Q|A", "2|2|R|A", "1,2|3|Q|1,2 ↔E" ]) (InvalidAt 3)
      ] )

  , ( "QN"
    , [ Case "negated universal becomes existential negation"
          (pf [ "1|1|¬∀xFx|A", "1|2|∃x¬Fx|1 QN" ]) Valid
      , Case "quantifier not switched"
          (pf [ "1|1|¬∀xFx|A", "1|2|∀x¬Fx|1 QN" ]) (InvalidAt 2)
      , Case "dependencies dropped"
          (pf [ "1|1|¬∀xFx|A", "|2|∃x¬Fx|1 QN" ]) (InvalidAt 2)
      ] )

  , ( "Proof structure"
    -- REGRESSION: with no ordering constraint, both lines below are locally
    -- correct, yet together they prove P from no assumptions at all.
    , [ Case "circular derivation: a line citing a later line"
          (pf [ "|1|P|2 ∧E", "|2|P∧P|1,1 ∧I" ]) (InvalidAt 1)
      , Case "a line citing itself"
          (pf [ "1|1|P|A", "1|2|P|2 ∧E" ]) (InvalidAt 2)
      , Case "duplicate line numbers"
          (pf [ "1|1|P|A", "1|1|Q|A" ]) (InvalidAt 1)
      , Case "forward reference to a line that does exist"
          (pf [ "1|1|P|A", "2|2|Q|A", "1,2|3|P∧Q|1,4 ∧I"
              , "4|4|R|A" ]) (InvalidAt 3)
      ] )

  , ( "Justification syntax"
    , [ Case "bare ∀I, variable inferred from the goal"
          (pf [ "1|1|P→∀xFx|A", "2|2|P|A", "1,2|3|∀xFx|1,2 MP"
              , "1,2|4|Fa|3 ∀E", "1|5|P→Fa|2,4 CP"
              , "1|6|∀x(P→Fx)|5 ∀I" ]) Valid
      , Case "∀I naming the correct variable"
          (pf [ "1|1|P→∀xFx|A", "2|2|P|A", "1,2|3|∀xFx|1,2 MP"
              , "1,2|4|Fa|3 ∀E", "1|5|P→Fa|2,4 CP"
              , "1|6|∀x(P→Fx)|5 ∀I x" ]) Valid
      , Case "∀I naming a variable the goal does not bind"
          (pf [ "1|1|P→∀xFx|A", "2|2|P|A", "1,2|3|∀xFx|1,2 MP"
              , "1,2|4|Fa|3 ∀E", "1|5|P→Fa|2,4 CP"
              , "1|6|∀x(P→Fx)|5 ∀I y" ]) ParseFails
      , Case "unknown rule name"
          (pf [ "1|1|P|A", "1|2|Q|1 XYZ" ]) ParseFails
      , Case "wrong number of columns"
          (pf [ "1|1|P" ]) ParseFails
      , Case "rule given the wrong number of line references"
          (pf [ "1|1|P→Q|A", "2|2|P|A", "1,2|3|Q|1 MP" ]) ParseFails
      ] )
  ]

--------------------------------------------------------------------------------
-- Runner
--------------------------------------------------------------------------------

main :: IO ()
main = do
  results <- mapM runGroup suite
  let total  = sum (map fst results)
      failed = sum (map snd results)
  putStrLn ""
  putStrLn (replicate 64 '-')
  if failed == 0
    then do
      putStrLn ("All " ++ show total ++ " cases behaved as expected.")
      exitSuccess
    else do
      putStrLn (show failed ++ " of " ++ show total ++ " cases misbehaved.")
      exitFailure

runGroup :: (String, [Case]) -> IO (Int, Int)
runGroup (rule, cs) = do
  putStrLn ""
  putStrLn (rule ++ ":")
  oks <- mapM runCase cs
  pure (length oks, length (filter not oks))

runCase :: Case -> IO Bool
runCase c = do
  let (ok, detail) = judge (caseText c) (caseExpect c)
  putStrLn ("  " ++ (if ok then "ok  " else "FAIL") ++ "  " ++ caseName c)
  forM_ detail (\d -> putStrLn ("          " ++ d))
  pure ok

-- | Decide a case, and on failure explain what happened instead.
judge :: String -> Expect -> (Bool, Maybe String)
judge txt expect =
  case parsePipeProof txt of

    Left e ->
      case expect of
        ParseFails -> (True, Nothing)
        _          -> (False, Just ("expected to parse, but: " ++ oneLine e))

    Right prf ->
      let bad = failingLines prf
      in case expect of

           ParseFails ->
             (False, Just ("expected a parse error, but it parsed and the \
                           \checker said " ++ verdict prf))

           Valid
             | null bad  -> (True, Nothing)
             | otherwise -> (False, Just ("expected valid, but line(s) "
                                          ++ commas bad ++ " failed: "
                                          ++ firstError prf))

           InvalidAt n
             | n `elem` bad -> (True, Nothing)
             | null bad     -> (False, Just ("expected line " ++ show n
                                             ++ " to fail, but the proof was accepted"))
             | otherwise    -> (False, Just ("expected line " ++ show n
                                             ++ " to fail, but the failing line(s) were "
                                             ++ commas bad ++ ": " ++ firstError prf))

failingLines :: Proof -> [Int]
failingLines prf = [ lrNum r | r <- checkProof prf, isLeft (lrNote r) ]
  where isLeft = either (const True) (const False)

firstError :: Proof -> String
firstError prf =
  case [ e | r <- checkProof prf, Left e <- [lrNote r] ] of
    (e:_) -> oneLine e
    []    -> ""

verdict :: Proof -> String
verdict prf = if proofValid (checkProof prf) then "valid" else "invalid"

commas :: [Int] -> String
commas = intercalate ", " . map show

oneLine :: String -> String
oneLine s = case lines s of
  (l:_) -> take 110 l
  []    -> s
