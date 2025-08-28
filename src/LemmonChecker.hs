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
import Data.List   (intercalate, replicate, find)

-- Returns Just "" when x not free and goal == body (no constant needed).
inferWitnessConst
  :: String        -- x (the bound variable of ∀x)
  -> PredFormula   -- body (of ∀x body)
  -> PredFormula   -- phi (the alleged instance)
  -> Maybe String  -- inferred constant symbol ("" = “no constant needed” case)
inferWitnessConst x body phi
  | not (x `Set.member` freeVars body) =
      if phi == body then Just "" else Nothing
  | otherwise =
      find
        (\c -> substFree x (Const c) body == phi)
        (Set.toList (getConsts phi))

-- | Strict check: given constant c, ensure φ == substFree x (Const c) body
checkUIWithConst
  :: String        -- ^ variable x
  -> String        -- ^ constant c
  -> PredFormula   -- ^ body of ∀x body
  -> PredFormula   -- ^ premise φ
  -> Either String ()
checkUIWithConst x c body phi =
  let expected = substFree x (Const c) body
  in if phi == expected
        then Right ()
        else Left $
          "UI error: expected instance " ++ show expected
          ++ " but got " ++ show phi

-- | Liberal UI check: if constant not explicitly given, infer it.
checkUILiberal
  :: String        -- ^ x
  -> PredFormula   -- ^ body of ∀x body
  -> PredFormula   -- ^ premise φ
  -> Either String String  -- ^ the constant actually used
checkUILiberal x body phi =
  case inferWitnessConst x body phi of
    Just c  -> case checkUIWithConst x c body phi of
                 Right () -> Right c
                 Left err -> Left err
    Nothing -> Left "UI error: could not infer which constant was generalized"          


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
        Nothing ->
          Left "❌ ∀ Elim refers to missing line"

        Just l1 ->
          case formula l1 of
            ForAll x body ->
              let goal = formula line in
              case inferWitnessConst x body goal of
                Nothing ->
                  Left "❌ ∀ Elim: goal is not a constant-instance of the ∀-body."
                Just _ ->
                  if references line == references l1
                    then Right ()
                    else Left "❌ ∀ Elim: dependencies must match the ∀ line."

            _ ->
              Left "❌ ∀ Elim expects a universally quantified formula (∀x φ)."

              

    ExistsIntro m ->
      case findLine m of
        Nothing ->
          Left "❌ ∃ Intro refers to missing line"

        Just l1 ->
          case formula line of
            Exists x body ->
              let premise = formula l1 in
              -- Does there exist a constant a with premise == substFree x (Const a) body?
              case inferWitnessConst x body premise of
                Nothing ->
                  Left "❌ ∃ Intro: the cited line is not an instance of the goal’s body (no constant a with φ[a/x] = premise)."
                Just _a ->
                  if references line == references l1
                     then Right ()
                     else Left "❌ ∃ Intro: dependencies must match the cited line."
            _ ->
              Left "❌ ∃ Intro expects an existentially quantified formula (∃x φ)."

    ForallIntro m ->
      case findLine m of
        Just l1 ->
          case formula line of
            ForAll x body ->
              case inferWitnessConst x body (formula l1) of
                Nothing ->
                  Left $ "❌ ∀ Intro: could not recognize the instance at line "
                      ++ show m ++ " as φ(" ++ x ++ "←c)."

                Just a ->
                  let occursInGamma = a `Set.member` freeConstsInAssumptions proof (references l1)
                      expectedRefs  = references l1
                      actualRefs    = references line
                      -- NEW: forbid any leftover occurrences of a in φ(x)
                      aInBody       = a `Set.member` (getConsts body)
                  in if aInBody
                       then Left $ "❌ ∀ Intro: constant \"" ++ a
                             ++ "\" still appears in φ(x). All occurrences must be generalized."
                     else if occursInGamma
                       then Left $ "❌ ∀ Intro: constant \"" ++ a
                             ++ "\" appears in undischarged assumptions "
                             ++ show (references l1)
                     else if actualRefs /= expectedRefs
                       then Left $ "❌ ∀ Intro: dependencies must match the instance line. "
                             ++ "Expected " ++ show (Set.toList expectedRefs)
                             ++ ", got "     ++ show (Set.toList actualRefs)
                     else Right ()
            _ ->
              Left $ "❌ ∀ Intro: goal at line "
                   ++ show (lineNumber line) ++ " is not a universal sentence."
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
              let phiA        = formula lAssume          -- supposed instance: φ(a)
                  psi         = formula lResult          -- result proved under the assumption
                  goal        = formula line             -- current line must repeat ψ
                  isAssumption = justification lAssume == Assumption

                  -- references: discharge the assumption m1 from lResult’s refs,
                  -- and carry over the ∃-line’s refs
                  refExists   = references lExists
                  refResult   = references lResult
                  deltaRefs   = Set.delete (lineNumber lAssume) refResult
                  expectedRefs = Set.union refExists deltaRefs

                  -- try to infer a constant a with phiA == substFree x (Const a) body
                  aMaybe      = inferWitnessConst x body phiA
              in
                if not isAssumption then
                  Left $ "❌ ∃ Elim: line " ++ show m1 ++ " must be an Assumption."
                else case aMaybe of
                  Nothing ->
                    Left $ "❌ ∃ Elim: the assumed instance at line " ++ show m1
                        ++ " is not of the form φ[a/x] for the ∃-body."
                  Just a ->
                    -- freshness side-condition for a:
                    --  (i) not in the ∃-body,
                    -- (ii) not in the final conclusion ψ,
                    --(iii) not in any undischarged assumptions (deltaRefs)
                    let inExistsBody   = a `Set.member` getConsts body
                        inGoalResult   = a `Set.member` getConsts psi
                        inOtherRefs    = a `Set.member` getConstsFromRefs proof deltaRefs

                        whereBad =
                          [ ("the ∃-formula’s body", inExistsBody)
                          , ("the conclusion ψ",      inGoalResult)
                          , ("undischarged assumptions " ++ show (Set.toList deltaRefs), inOtherRefs)
                          ]
                        badPlaces = [ place | (place, True) <- whereBad ]
                    in if not (null badPlaces) then
                         Left $ "❌ ∃ Elim: the witness constant \"" ++ a ++ "\" must be fresh, "
                             ++ "but it occurs in " ++ unwords (map (\p -> "[" ++ p ++ "]") badPlaces) ++ "."
                       else if goal /= psi then
                         Left $ "❌ ∃ Elim: the conclusion at line " ++ show (lineNumber line)
                             ++ " must repeat ψ from line " ++ show n ++ "."
                       else if references line /= expectedRefs then
                         Left $ "❌ ∃ Elim: incorrect references.\n"
                             ++ "  Expected: " ++ show (Set.toList expectedRefs) ++ "\n"
                             ++ "  Found:    " ++ show (Set.toList (references line))
                       else
                         Right ()
            _ ->
              Left $ "❌ ∃ Elim: line " ++ show m ++ " must contain an existential formula (∃x φ)."
        _ ->
          Left "❌ ∃ Elim refers to missing lines."    


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

