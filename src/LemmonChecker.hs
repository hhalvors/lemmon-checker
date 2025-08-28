-- LemmonChecker.hs
module LemmonChecker
     ( checkProof      
     , printReport
     , proofValid
     , LineReport(..) 
     ) where

import ProofTypes
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)
import Debug.Trace (trace)
import           Control.Monad   (forM_)
import           Text.Printf      (printf)
import PrettyPrint (renderFormula)
import Data.List   (intercalate, replicate)

checkInstanceSubstitution
  :: String                -- ^ x: the bound variable
  -> PredFormula           -- ^ φ(x): the quantified body
  -> PredFormula           -- ^ φ(a): the instance
  -> Either String String  -- ^ Either an error or the constant “a”
checkInstanceSubstitution x phiX phiA =
  case matchSubstitution x phiX phiA of
    -- Matched with a constant witness ‘a’
    Just (Const a) ->
      let constsInPhiX = getConsts phiX
      in if a `Set.member` constsInPhiX
           then Left $
                "Substitution invalid: constant \"" ++ a
                ++ "\" still appears in φ(x). All instances must be replaced."
           else Right a

    -- Matched, but the witness term is not a constant
    Just other ->
      Left $
        "Substitution invalid: instance uses a non-constant term "
        ++ show other ++ " (not allowed for UI or EE)."

    -- No match at all
    Nothing ->
      Left $
        "Substitution failed: could not match φ(a) as an instance of φ(x).\n"
        ++ "φ(x): " ++ show phiX ++ "\nφ(a): " ++ show phiA


mpExpected :: ProofLine -> ProofLine -> Either String (PredFormula, Set.Set Int)
mpExpected l1 l2 =
  case formula l1 of
    Implies p q ->
      if formula l2 /= p
        then Left "The second cited line of MP must be the antecedent of the conditional."
        else Right (q, Set.union (references l1) (references l2))
    _ ->
      Left "The first cited line of MP must be a conditional."



checkLine :: Proof -> ProofLine -> Either String ()
checkLine proof line =
  case justification line of

    Assumption ->
      if references line == Set.singleton (lineNumber line)
        then Right ()
        else Left $ "❌ Invalid assumption at line " ++ show (lineNumber line)

    MP m n ->
      case (findLine m, findLine n) of
        (Just l1, Just l2) ->
          case mpExpected l1 l2 of
            Left msg ->
              Left $ "❌ " ++ msg ++ " (at line " ++ show (lineNumber line) ++ ")"
            Right (q, deps) ->
              if formula line /= q
                then Left $ "❌ The formula on the inferred line must be the consequent of the conditional "
                         ++ "(expected " ++ show q ++ ")."
              else if references line /= deps
                then Left $ "❌ The dependencies of MP must be the union of the cited lines' dependencies."
              else Right ()
        _ ->
          Left "❌ MP requires valid line references."

    MT m n ->
      case (findLine m, findLine n) of
        (Just l1, Just l2) ->
          let f1 = formula l1
              f2 = formula l2
              goal = formula line
              expectedRefs = Set.union (references l1) (references l2)
              actualRefs   = references line

              matchesMT = case (f1, f2, goal) of
                (Implies phi psi, Not psi', Not phi') -> psi == psi' && phi == phi'
                (Not psi', Implies phi psi, Not phi') -> psi == psi' && phi == phi'
                _ -> False

              depsOK = actualRefs == expectedRefs
  
          in if matchesMT && depsOK
             then Right ()
             else
               let msg1 = if not matchesMT
                          then "Formula pattern does not match Modus Tollens"
                          else ""
                   msg2 = if not depsOK
                          then "Dependencies on line " ++ show (lineNumber line) ++
                               " are not the union of dependencies on lines " ++
                               show m ++ " and " ++ show n
                          else ""
                   msg = intercalate ". " (filter (not . null) [msg1, msg2])
               in Left $ "❌ Invalid MT at line " ++ show (lineNumber line) ++ ": " ++ msg
        _ -> Left $ "❌ MT refers to missing lines"

    DN m ->
      case findLine m of
        Just l1 ->
            let phi1 = formula l1
                phi2 = formula line
            in case (phi1, phi2) of
                (Not (Not inner), phi)
                    | phi == inner ->
                        if references line == references l1
                            then Right ()
                            else Left $ "❌ Incorrect references in DN at line " ++ show (lineNumber line)
                (phi, Not (Not inner))
                    | phi == inner ->
                        if references line == references l1
                            then Right ()
                            else Left $ "❌ Incorrect references in DN at line " ++ show (lineNumber line)
                _ ->
                    Left $ "❌ DN requires φ and ¬¬φ on one of the lines (either direction) at line " ++ show (lineNumber line)
        Nothing ->
            Left $ "❌ DN refers to missing line " ++ show m

    AndElim m ->
      case findLine m of
        Just l1 ->
          case formula l1 of
            And f1 f2 ->
              if formula line == f1 || formula line == f2
                 then if references line == references l1
                        then Right ()
                        else Left $ "❌ Incorrect references in ∧ Elim at line " ++ show (lineNumber line)
                 else Left $ "❌ Goal is not one conjunct of ∧ at line " ++ show (lineNumber line)
            _ -> Left $ "❌ ∧ Elim requires ∧ formula at line " ++ show m
        Nothing -> Left $ "❌ ∧ Elim refers to missing line"

    OrIntro m ->
      case findLine m of
        Just l1 ->
          case formula line of
            Or f1 f2 ->
              let base = formula l1
              in if base == f1 || base == f2
                   then if references line == references l1
                          then Right ()
                          else Left $ "❌ Incorrect references in ∨ Intro"
                   else Left $ "❌ ∨ Intro formula must contain cited formula as a disjunct"
            _ -> Left $ "❌ Goal is not a disjunction"
        Nothing -> Left $ "❌ ∨ Intro refers to missing line"

    OrElim m m1 n1 m2 n2 ->
      case (findLine m, findLine m1, findLine n1, findLine m2, findLine n2) of
        (Just d, Just a1, Just c1, Just a2, Just c2) ->
          let goal = formula line
              disj = formula d
              a1f = formula a1
              a2f = formula a2
              g1  = formula c1
              g2  = formula c2

              allSameGoal = goal == g1 && goal == g2
              notDisjunction = case disj of
                                 Or _ _ -> False
                                 _      -> True
              disjOk = case disj of
                         Or p q -> (a1f == p && a2f == q) || (a1f == q && a2f == p)
                         _ -> False
              a1ok = justification a1 == Assumption
              a2ok = justification a2 == Assumption

              delta1 = Set.delete (lineNumber a1) (references c1)
              delta2 = Set.delete (lineNumber a2) (references c2)
              gamma  = references d
              refsExpected = gamma `Set.union` delta1 `Set.union` delta2
              refsActual   = references line

              errors =
                [ "🚫 Formula on line " ++ show (lineNumber d) ++ " is not a disjunction."
                    | notDisjunction ] ++
                [ "🚫 The conclusion does not match both subproof conclusions."
                    | not allSameGoal ] ++
                [ "🚫 Disjunction in line " ++ show (lineNumber d) ++
                  " does not match assumptions on lines " ++ show (lineNumber a1) ++ " and " ++ show (lineNumber a2)
                    | not disjOk ] ++
                [ "🚫 Line " ++ show (lineNumber a1) ++ " is not an assumption." | not a1ok ] ++
                [ "🚫 Line " ++ show (lineNumber a2) ++ " is not an assumption." | not a2ok ] ++
                [ "🚫 Dependencies on line " ++ show (lineNumber line) ++ " are incorrect."
                    | refsActual /= refsExpected ]

          in if null errors
               then Right ()
               else Left $ "❌ Invalid ∨ Elim at line " ++ show (lineNumber line) ++ ":\n" ++ unlines errors

        _ -> Left $ "❌ ∨ Elim requires five valid lines"    

    RAA m n ->
      case (findLine m, findLine n) of
        (Just lAssume, Just lContradiction) ->
          let φ     = formula lAssume
              goal  = formula line
              refsN = references lContradiction
              expectedRefs = Set.delete (lineNumber lAssume) refsN
              contradiction = formula lContradiction
              isContradiction = case contradiction of
                And ψ (Not ψ') -> ψ == ψ'
                And (Not ψ) ψ' -> ψ == ψ'
                _              -> False
              validGoal = goal == Not φ
              validAssumption = justification lAssume == Assumption
          in if validAssumption && isContradiction && validGoal && references line == expectedRefs
               then Right ()
               else Left $ "❌ Invalid RAA at line " ++ show (lineNumber line) ++
                           (if not validAssumption
                             then "\n  🚫 Line " ++ show m ++ " must be an assumption."
                             else "") ++
                           (if not isContradiction
                             then "\n  🚫 Line " ++ show n ++ " must be a contradiction (ψ ∧ ¬ψ)."
                             else "") ++
                           (if not validGoal
                             then "\n  🧠 Goal must be the negation of formula on line " ++ show m
                             else "") ++
                           (if references line /= expectedRefs
                             then "\n  📎 Expected references: " ++ show (Set.toList expectedRefs) ++
                                  "\n  But got: " ++ show (Set.toList (references line))
                             else "")
        _ -> Left $ "❌ RAA refers to non-existent lines " ++ show m ++ " or " ++ show n        

    ForallElim m ->
      case findLine m of
        Just l1 ->
          case formula l1 of
            ForAll x body ->
              let goal = formula line
              in case matchSubstitution x body goal of
                   Just _ ->
                     if references line == references l1
                       then Right ()
                       else Left $ "❌ Incorrect references in ∀ Elim"
                   Nothing -> Left $ "❌ ∀ Elim substitution failed"
            _ -> Left $ "❌ ∀ Elim expects ∀ formula"
        Nothing -> Left $ "❌ ∀ Elim refers to missing line"

    ExistsIntro m ->
      case findLine m of
        Just l1 ->
          case formula line of
            Exists x body ->
              case matchSubstitution x body (formula l1) of
                Just _ ->
                  if references line == references l1
                    then Right ()
                    else Left $ "❌ Incorrect references in ∃ Intro"
                Nothing -> Left $ "❌ ∃ Intro substitution failed"
            _ -> Left $ "❌ Goal is not ∃ formula"
        Nothing -> Left $ "❌ ∃ Intro refers to missing line"

    ForallIntro m x ->
      case findLine m of
        Just l1 ->
          case formula line of
            -- goal must be ∀x φ
            ForAll y body | y == x ->
              case checkInstanceSubstitution x body (formula l1) of
                -- substitution inside the quantified body failed
                Left err ->
                  Left $ "❌ ∀ Intro: " ++ err
                         ++ " (line " ++ show (lineNumber line) ++ ")"

                -- substitution succeeded with witness constant a
                Right a ->
                  let occursInGamma = a `Set.member` freeConstsInAssumptions proof (references l1)
                      expectedRefs = references l1
                      actualRefs   = references line
                  in if occursInGamma
                     then Left $ "❌ ∀ Intro: constant \"" ++ a
                          ++ "\" appears in undischarged assumptions "
                          ++ show (references l1)
                     else if actualRefs /= expectedRefs
                          then Left $ "❌ ∀ Intro: dependencies must match the instance line. "
                               ++ "Expected " ++ show (Set.toList expectedRefs)
                               ++ ", got "     ++ show (Set.toList actualRefs)
                          else Right ()

            -- goal line is not a universal quantification in x
            _ -> Left $ "❌ ∀ Intro: goal at line "
                        ++ show (lineNumber line)
                        ++ " is not ∀" ++ x ++ " φ"

        -- the cited instance line is missing
        Nothing ->
          Left $ "❌ ∀ Intro refers to missing line " ++ show m    

    CP from to ->
      case (findLine from, findLine to) of
        (Just lFrom, Just lTo) ->
          let phi = formula lFrom
              psi = formula lTo
              goal = formula line
              depsExpected = Set.delete (lineNumber lFrom) (references lTo)
              valid =
                justification lFrom == Assumption &&
                goal == Implies phi psi &&
                references line == depsExpected
          in if valid
               then Right ()
               else Left $ "❌ Invalid CP at line " ++ show (lineNumber line)
        _ -> Left $ "❌ CP refers to missing lines"

    ExistsElim m m1 n ->
      case (findLine m, findLine m1, findLine n) of
        (Just lExists, Just lAssume, Just lResult) ->
          case formula lExists of
            Exists x body ->
              let phiA = formula lAssume
                  psi = formula lResult
                  goal = formula line
                  refExists = references lExists
                  refResult = references lResult
                  deltaRefs = Set.delete (lineNumber lAssume) refResult
                  expectedRefs = Set.union refExists deltaRefs

                  isAssumption = justification lAssume == Assumption
                  sameGoal = formula line == psi

                  constMaybe = matchSubstitution x body phiA
              in case constMaybe of
                   Just t@(Const a) ->
                     let inExistsLine = a `Set.member` getConsts body
                         inGoal = a `Set.member` getConsts psi
                         inOtherRefs = a `Set.member` getConstsFromRefs proof deltaRefs

                         violations = concat
                           [ ["line " ++ show (lineNumber lExists) ++ " (∃-formula) | " | inExistsLine]
                           , ["line " ++ show (lineNumber lResult) ++ " (goal) | " | inGoal]
                           , ["undischarged assumptions in lines " ++ show (Set.toList deltaRefs) ++ " | " | inOtherRefs]
                           ]

                     in if not isAssumption
                          then Left $ "❌ ∃ Elim: line " ++ show m1 ++ " must be an assumption"
                          else if not sameGoal
                            then Left $ "❌ ∃ Elim: conclusion at line " ++ show (lineNumber line) ++ " does not match ψ from line " ++ show n
                            else if not (null violations)
                              then Left $ "❌ ∃ Elim: constant " ++ a ++ " must be fresh — but it appears in: " ++ concat violations
                              else if references line /= expectedRefs
                                then Left $ "❌ ∃ Elim: incorrect references at line " ++ show (lineNumber line) ++
                                            "\nExpected: " ++ show (Set.toList expectedRefs) ++
                                            "\nFound: " ++ show (Set.toList (references line))
                                else Right ()

                   _ ->
                     let constsInBody = getConsts body
                         constsInPhiA = getConsts phiA
                         overlap = Set.toList (Set.intersection constsInBody constsInPhiA)
                     in Left $
                          "❌ ∃ Elim: substitution failed at line " ++ show (lineNumber line) ++
                          ". The constant(s) used in φ(a) also occur in the ∃ formula φ(x): " ++
                          show overlap ++ "\n→ This violates the restriction that the witness must be fresh."
            _ -> Left $ "❌ ∃ Elim: line " ++ show m ++ " must contain ∃ formula"
        _ -> Left $ "❌ ∃ Elim refers to missing lines"        

    _ -> Right ()

  where
    findLine k = lookup k [(lineNumber l, l) | l <- proof]

-- Finite search for a matching term t --------------------------------
-- We consider candidate terms drawn from variables/constants that appear
-- in either formula (you can widen/narrow this set as you like).
matchSubstitution :: String -> PredFormula -> PredFormula -> Maybe Term
matchSubstitution x phi psi =
  let candVars   = Set.toList (varsInFormula phi `Set.union` varsInFormula psi)
      candConsts = Set.toList (constsInFormula phi `Set.union` constsInFormula psi)
      candidates = map Var candVars ++ map Const candConsts
  in
    findFirst (\t -> freeFor x t phi && substFree x t phi == psi) candidates

-- tiny helper
findFirst :: (a -> Bool) -> [a] -> Maybe a
findFirst _ [] = Nothing
findFirst p (z:zs)
  | p z       = Just z
  | otherwise = findFirst p zs    



orElse :: Maybe a -> Maybe a -> Maybe a
orElse (Just x) _ = Just x
orElse Nothing y  = y

getConsts :: PredFormula -> Set String
getConsts (Predicate _ terms) = Set.unions (map getConst terms)
getConsts (Boolean _) = Set.empty
getConsts (Not f) = getConsts f
getConsts (And f g) = Set.union (getConsts f) (getConsts g)
getConsts (Or f g) = Set.union (getConsts f) (getConsts g)
getConsts (Implies f g) = Set.union (getConsts f) (getConsts g)
getConsts (ForAll _ f) = getConsts f
getConsts (Exists _ f) = getConsts f

getConst :: Term -> Set String
getConst (Const a) = Set.singleton a
getConst (Var _)   = Set.empty

freeConstsInAssumptions :: Proof -> Set Int -> Set String
freeConstsInAssumptions proof refs = Set.unions
  [ getConsts (formula l)
  | l <- proof
  , lineNumber l `Set.member` refs
  , justification l == Assumption
  ]

getConstsFromRefs :: Proof -> Set Int -> Set String
getConstsFromRefs proof refs = Set.unions
  [ getConsts (formula l)
  | l <- proof
  , lineNumber l `Set.member` refs
  ]

data LineReport = LineReport
  { lrNum  :: Int
  , lrLine :: ProofLine
  , lrNote :: Either String ()  
  }

type ProofReport = [LineReport]

-- | Convert an entire proof to a full report (no early exit)
checkProof :: Proof -> ProofReport
checkProof proof =
  [ LineReport (lineNumber ln) ln (checkLine proof ln) | ln <- proof ]

-- | Is the whole proof valid?
proofValid :: ProofReport -> Bool
proofValid = all (either (const False) (const True) . lrNote)

printReport :: ProofReport -> IO ()
printReport reps = do
  putStrLn ""
  putStrLn "Deps     Line   Formula                                  Justification           Result"
  putStrLn "-------  -----  ---------------------------------------  -----------------------  -------------------------"
  forM_ reps printOne
  where
    ----------------------------------------------------------------
    -- One row (plus optional wrapped error text)
    ----------------------------------------------------------------
    printOne :: LineReport -> IO ()
    printOne (LineReport n l note) = do
      let baseRow = printf "%-7s %-6s %-39s %-23s "
                          (deps l)
                          (ln n)
                          (short (renderFormula (formula l)))
                          (justTxt (justification l))

          resultMsg = case note of
                        Right _     -> ["✅  Valid"]
                        Left errMsg -> wrapWords resultWidth ("❌  " ++ errMsg)

      -- Print first line of result alongside base row
      putStrLn $ baseRow ++ head resultMsg

      -- Print any additional lines of result, fully indented
      mapM_ (putStrLn . indentRow) (tail resultMsg)

      where
        resultWidth = 25

        indentRow :: String -> String
        indentRow msg = printf "%-7s %-6s %-39s %-23s %s" "" "" "" "" msg

    ----------------------------------------------------------------
    -- Helpers
    ----------------------------------------------------------------
    deps :: ProofLine -> String
    deps l =
      let xs = Set.toList (references l)
      in if null xs then "∅" else intercalate "," (map show xs)

    ln :: Int -> String
    ln = printf "(%d)"           -- “(3)”, “(12)”, …

    short :: String -> String
    short s = if length s > 38 then take 35 s ++ "…" else s

    justTxt :: Justification -> String
    justTxt j = take 23 $ show j ++ repeat ' '

    -- Word-wrap a string to lines of max width
    wrapWords :: Int -> String -> [String]
    wrapWords _ "" = []
    wrapWords n s  = wrapWords' n (words s)

    wrapWords' :: Int -> [String] -> [String]
    wrapWords' _ [] = []
    wrapWords' n ws =
      let (line, rest) = takeLine n ws
      in unwords line : wrapWords' n rest

    takeLine :: Int -> [String] -> ([String], [String])
    takeLine _ [] = ([], [])
    takeLine n (w:ws)
      | length w > n = ([take n w ++ "…"], ws)  -- truncate a single long word
      | otherwise = go (length w) [w] ws
      where
        go _ acc [] = (reverse acc, [])
        go len acc (w':ws')
          | len + 1 + length w' <= n = go (len + 1 + length w') (w' : acc) ws'
          | otherwise = (reverse acc, w':ws')

