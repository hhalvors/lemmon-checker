-- FitchConvert.hs
--
-- Translation between the Lemmon proofs of How Logic Works and the Fitch
-- presentation in FitchTypes.
--
-- The two directions are not equally hard, and it is worth being explicit
-- about why, because the asymmetry is a fact about the notations rather than
-- about this implementation.
--
-- FITCH TO LEMMON is total. Walk the proof and compute each line's dependency
-- set as the union of the sets of the lines it cites, less whatever the rule
-- discharges. Nothing can fail: Fitch's box structure always determines a
-- legitimate Lemmon bookkeeping. The set it produces is the *minimal* one,
-- which is a little more information than the Fitch proof displayed — a line
-- sitting inside a box it never used comes out with the smaller set. So the
-- round trip Fitch → Lemmon → Fitch is a normalisation, not the identity: it
-- can return a proof with tighter boxes than it was given.
--
-- LEMMON TO FITCH can fail, for a reason more specific than "subproofs need
-- not be stacked linearly". Two obstructions, and only the second is deep:
--
--   1. Discharge order. Fitch can only close the innermost open box, whereas
--      Lemmon may discharge assumptions in any order. Assume P, assume Q,
--      discharge P, discharge Q is a perfectly good Lemmon proof and has no
--      direct Fitch image. It does have an indirect one — permute the two
--      assumptions, since neither depends on the other — so this obstruction
--      is a matter of reordering, and reordering is always available in
--      principle.
--
--   2. Scope is coarser than dependency. A line written between an
--      assumption and its discharge sits inside that box, and dies when the
--      box closes — even if it never depended on the assumption. In Lemmon it
--      survives the discharge untouched, because a Lemmon line's position in
--      the text has no bearing on what it depends on.
--
--      Note what the remedy is, since an earlier draft of this comment got it
--      wrong. It is not that the line must be derived twice. It is that the
--      line is in the wrong *place*, and needs hoisting to a box shallow
--      enough to outlive the discharge. Both obstruction cases in the test
--      corpus translate through the tree with no growth at all — five lines
--      to five, six to six — because the tree has no notion of "written
--      between these two lines" for a line to be caught by.
--
--      Whether duplication is ever strictly necessary is open. If L is cited
--      by M then L's dependencies are among M's, so placing every line at the
--      depth of its deepest dependency puts it above all of its users, which
--      suggests it is not. Unfolding a shared line still copies it here; that
--      is the algorithm being simple, not the notations demanding it.
--
-- Both obstructions come to the same thing, and it is worth stating precisely
-- rather than by the usual slogan that Lemmon proofs are graphs and Fitch
-- proofs are trees. That is not right: a Fitch proof shares lines too, since
-- two lines in one subproof may both cite an earlier line in it.
--
-- What is true is this. The object both notations record is a derivation,
-- which is a tree. Both present it as a directed acyclic graph, by writing
-- each line once and citing it thereafter -- that is what sharing is. The
-- difference is in which sharing each permits. Lemmon permits any line to be
-- cited by any later line whatever: nothing ever goes out of scope, because
-- discharging alters the dependency set of a new line and touches no line
-- already written. Fitch permits citation only along the paths its nesting of
-- subproofs allows, and a line becomes unavailable for good once its subproof
-- closes.
--
-- So translating means finding a nesting that accommodates all the sharing the
-- source uses. The two obstructions are the two ways no such nesting exists.
-- Unfolding removes the sharing, and a graph without sharing is a tree, which
-- constrains nothing -- there is no shared line left to be shared wrongly.
--
-- What is implemented here is the direct, non-duplicating translation: it
-- succeeds on any Lemmon proof whose discharge structure already nests, which
-- covers essentially every textbook proof, and it reports precisely which of
-- the two obstructions it hit when it fails. It does not yet reorder, and it
-- does not duplicate. Both are additions on top of this, not rewrites of it.

module FitchConvert
  ( fitchToLemmon
  , lemmonToFitch
  , lemmonToFitchDirect
  , Route(..)
  , toDerivation
  , derivationToFitch
  , Deriv(..)
  , DRule(..)
  , TranslationError(..)
  , renderTranslationError
  ) where

import ProofTypes
import FitchTypes

import qualified Data.Map.Strict as M
import qualified Data.Set        as S
import           Data.List       (sort)

--------------------------------------------------------------------------------
-- Fitch to Lemmon
--------------------------------------------------------------------------------

-- | Flatten a Fitch proof into Lemmon lines.
--
-- Line numbers carry over unchanged: item n in the Fitch proof becomes line n
-- of the Lemmon proof. The dependency sets are computed, not read off.
fitchToLemmon :: FitchProof -> Proof
fitchToLemmon prf = reverse (snd (foldl item (M.empty, []) prf))
  where
    -- The map is line number to dependency set, threaded through so that a
    -- later line can look up what it cites. The list accumulates in reverse.
    item :: (M.Map Int (S.Set Int), Proof) -> FitchItem -> (M.Map Int (S.Set Int), Proof)
    item (deps, acc) (FLine n f r) =
      let d  = depsOf deps r n
          l  = ProofLine { lineNumber    = n
                         , formula       = f
                         , justification = toLemmonRule r
                         , references    = d }
      in (M.insert n d deps, l : acc)

    item (deps, acc) (FSub s) =
      let a   = subAssumeLine s
          l   = ProofLine { lineNumber    = a
                          , formula       = subAssumeForm s
                          , justification = Assumption
                          , references    = S.singleton a }
          st0 = (M.insert a (S.singleton a) deps, l : acc)
      in foldl item st0 (subBody s)

    -- The dependency set of a line, given the sets of everything before it.
    -- Discharge rules subtract the assumption their subproof opened; every
    -- other rule takes the union of what it cites.
    depsOf :: M.Map Int (S.Set Int) -> FitchRule -> Int -> S.Set Int
    depsOf deps r self =
      case r of
        FPremise         -> S.singleton self
        FAssume          -> S.singleton self
        FCP (a, c)       -> S.delete a (look c)
        FRAA (a, c)      -> S.delete a (look c)
        FOrE d (a1,c1) (a2,c2) ->
          S.unions [ look d, S.delete a1 (look c1), S.delete a2 (look c2) ]
        FExistsE m (a, c) -> look m `S.union` S.delete a (look c)
        _                 -> S.unions (map look (citedLines (toLemmonRule r)))
      where
        look n = M.findWithDefault S.empty n deps

-- | The Lemmon justification corresponding to a Fitch rule. A subproof
-- reference becomes the pair of line numbers the Lemmon rules already use.
toLemmonRule :: FitchRule -> Justification
toLemmonRule r =
  case r of
    FPremise               -> Assumption
    FAssume                -> Assumption
    FMP m n                -> MP m n
    FMT m n                -> MT m n
    FDN m                  -> DN m
    FCP (a, c)             -> CP a c
    FAndI m n              -> AndIntro m n
    FAndE m                -> AndElim m
    FOrI m                 -> OrIntro m
    FOrE d (a1,c1) (a2,c2) -> OrElim d a1 c1 a2 c2
    FRAA (a, c)            -> RAA a c
    FForallE m             -> ForallElim m
    FForallI m             -> ForallIntro m
    FExistsI m             -> ExistsIntro m
    FExistsE m (a, c)      -> ExistsElim m a c
    FEqI                   -> EqIntro
    FEqE m n               -> EqElim m n
    FLEM                   -> LEM
    FPropTaut ms           -> PropTaut ms
    FIffI m n              -> IffIntro m n
    FIffE m n              -> IffElim m n
    FQN m                  -> QN m
    -- Reiteration repeats a line; the repeat follows from it
    -- tautologically, which is a justification Lemmon does have.
    FReit m                -> PropTaut [m]

--------------------------------------------------------------------------------
-- Lemmon to Fitch
--------------------------------------------------------------------------------

data TranslationError
  = NotNested Int Int [Int]
    -- ^ line, the assumption it discharges, the open assumptions innermost
    --   first. The assumption discharged is not the innermost one.
  | OutOfScope Int Int Int
    -- ^ line, the line it cites, the assumption whose box closed over the
    --   cited line. This is obstruction 2: the cited line was trapped.
  | UnknownAssumption Int Int
    -- ^ line, the assumption line it names, which is not open here
  | MissingLine Int
    -- ^ a citation to a line that does not exist
  | EigenInScope Int String Int
    -- ^ line, the name generalised upon, the enclosing assumption in which it
    --   occurs. Lemmon tests arbitrariness against the dependency set; Fitch
    --   can only test it against scope, which may be larger.
  | PremiseInBox Int Int
    -- ^ line, the innermost open assumption. An assumption that is never
    --   discharged is a premise, and a premise must sit at the outermost
    --   level; but Lemmon lets one be written anywhere, including between
    --   another assumption and its discharge.
  | Internal String
  deriving (Show, Eq)

renderTranslationError :: TranslationError -> String
renderTranslationError e =
  case e of
    NotNested l a open ->
      "Line " ++ show l ++ " discharges assumption " ++ show a
      ++ ", but the innermost open assumption is "
      ++ (case open of { (x:_) -> show x; [] -> "none" })
      ++ " (open: " ++ show open ++ "). Fitch can only close the innermost "
      ++ "box, so this proof needs its assumptions reordered before it has a "
      ++ "Fitch image."
    OutOfScope l cited a ->
      "Line " ++ show l ++ " cites line " ++ show cited ++ ", which sits "
      ++ "inside the box opened by assumption " ++ show a ++ ". That box has "
      ++ "closed, so in Fitch the line is no longer available -- even though "
      ++ "in Lemmon it never depended on " ++ show a ++ ". Translating this "
      ++ "proof requires deriving line " ++ show cited ++ " a second time."
    UnknownAssumption l a ->
      "Line " ++ show l ++ " discharges assumption " ++ show a
      ++ ", which is not an open assumption at that point."
    MissingLine n ->
      "Citation to line " ++ show n ++ ", which does not appear in the proof."
    EigenInScope l c a ->
      "Line " ++ show l ++ " generalises on the name " ++ c ++ ", which does "
      ++ "not occur in any assumption the line depends on -- so Lemmon "
      ++ "licenses it. But it occurs in assumption " ++ show a ++ ", which is "
      ++ "in scope here, and Fitch tests arbitrariness against scope. The "
      ++ "subderivation must be renamed to a fresh name first."
    PremiseInBox l a ->
      "Line " ++ show l ++ " is an assumption that is never discharged, so in "
      ++ "Fitch it is a premise -- but it is written inside the subproof "
      ++ "opened by assumption " ++ show a ++ ", and a premise must stand at "
      ++ "the outermost level. The premises have to be gathered at the top, "
      ++ "which renumbers the proof."
    Internal m -> "Internal error in the translation: " ++ m

-- | Where each line sits: the set of box-opening assumptions enclosing it at
-- the moment it is written. This is what decides reachability, and it is
-- *not* the dependency set — a line with no dependencies at all can still be
-- written inside a box, and is then just as trapped as anything else in it
-- when that box closes.
type Placement = M.Map Int (S.Set Int)

data St = St
  { stStack  :: [(Int, PredFormula, [FitchItem])]  -- ^ open boxes, innermost first
  , stAcc    :: [FitchItem]                        -- ^ items at this level, reversed
  , stPlaced :: Placement
  , stSubs   :: M.Map Int SubRef                   -- ^ boxes already closed
  }

-- | Translate a Lemmon proof into Fitch, without reordering or duplicating.
--
-- A box is closed at the line the proof says it ends on, not at the line of
-- the rule that cites it. That distinction matters for disjunction
-- elimination: its two cases are siblings, and the first must close before
-- the second is assumed. Closing both at the ∨E line would nest them.
lemmonToFitchDirect :: Proof -> Either TranslationError FitchProof
lemmonToFitchDirect prf = reverse <$> go prf (St [] [] M.empty M.empty)
  where
    -- Assumption line to the last line of the box it opens. Assumptions not
    -- in this map are never discharged, and become premises rather than
    -- boxes that never close.
    boxEnd :: M.Map Int Int
    boxEnd = M.fromList $ concat
      [ case justification l of
          CP a c               -> [(a, c)]
          RAA a c              -> [(a, c)]
          ExistsElim _ a c     -> [(a, c)]
          OrElim _ a1 c1 a2 c2 -> [(a1, c1), (a2, c2)]
          _                    -> []
      | l <- prf ]

    known :: S.Set Int
    known = S.fromList (map lineNumber prf)

    byNum :: M.Map Int ProofLine
    byNum = M.fromList [ (l, ln) | ln <- prf, let l = lineNumber ln ]

    -- The eigenvariable condition, tested the way Fitch has to test it.
    --
    -- The names generalised upon are those occurring in the cited formula and
    -- not in the conclusion: abstraction replaces every occurrence, so a name
    -- that is generalised cannot survive into the goal.
    checkEigen :: Int -> Int -> PredFormula -> St -> Either TranslationError ()
    checkEigen n m goal st =
      case M.lookup m byNum of
        Nothing  -> Left (MissingLine m)
        Just src ->
          let eig = constsInFormula (formula src)
                      `S.difference` constsInFormula goal
              bad = [ (c, a)
                    | (a, af, _) <- stStack st
                    , c <- S.toList eig
                    , c `S.member` constsInFormula af ]
          in case bad of
               ((c, a) : _) -> Left (EigenInScope n c a)
               []           -> Right ()

    go :: [ProofLine] -> St -> Either TranslationError [FitchItem]

    go [] st =
      -- A box still open at the end means the proof stopped inside a
      -- subproof. Fold them up rather than dropping the lines, so the result
      -- is a faithful picture of an unfinished proof instead of a silent lie.
      pure (foldl closeOpen (stAcc st) (stStack st))
      where
        closeOpen inner (a, f, outer) = FSub (Subproof a f (reverse inner)) : outer

    go (l : rest) st = do
      let n     = lineNumber l
          j     = justification l
          scope = openSet st

      -- Obstruction 2. Only citations made from outside a closing box are
      -- checked: a discharge rule cites the box it closes, which is legal by
      -- definition, so those are exempt.
      mapM_ (reachable n scope (stPlaced st)) (outerCitations j)

      st1 <- case j of
        Assumption
          | n `M.member` boxEnd ->
              -- Opens a box; the assumption line itself sits inside it.
              pure st { stStack  = (n, formula l, stAcc st) : stStack st
                      , stAcc    = []
                      , stPlaced = M.insert n (S.insert n scope) (stPlaced st) }
          -- An undischarged assumption is a premise, and Fitch premises live
          -- at the outermost level only. Writing one here would put it inside
          -- a box, which recomputes to the right dependency set and is still
          -- not a Fitch proof: the box would appear to derive the premise
          -- from its assumption.
          | not (null (stStack st)) ->
              Left (PremiseInBox n (head [ a | (a,_,_) <- stStack st ]))
          | otherwise ->
              pure (emit n (formula l) FPremise scope st)
        _ -> do
          r <- ruleFor n j (stSubs st)
          case j of
            ForallIntro m -> checkEigen n m (formula l) st
            _             -> pure ()
          pure (emit n (formula l) r scope st)

      st2 <- closeBoxes n st1
      go rest st2

    openSet :: St -> S.Set Int
    openSet = S.fromList . map (\(a,_,_) -> a) . stStack

    emit :: Int -> PredFormula -> FitchRule -> S.Set Int -> St -> St
    emit n f r scope st =
      st { stAcc    = FLine n f r : stAcc st
         , stPlaced = M.insert n scope (stPlaced st) }

    -- Close every box whose last line is the one just written, innermost
    -- first. If an *outer* box claims to end here while an inner one is
    -- still open, the proof discharges out of order and has no direct Fitch
    -- image.
    closeBoxes :: Int -> St -> Either TranslationError St
    closeBoxes n st0 = do
      st' <- loop st0
      case [ a | (a,_,_) <- stStack st', M.lookup a boxEnd == Just n ] of
        (a : _) -> Left (NotNested n a (map (\(x,_,_) -> x) (stStack st')))
        []      -> pure st'
      where
        loop st =
          case stStack st of
            ((a, f, outer) : rest)
              | M.lookup a boxEnd == Just n ->
                  let s = Subproof a f (reverse (stAcc st))
                  in loop st { stStack = rest
                             , stAcc   = FSub s : outer
                             , stSubs  = M.insert a (subAssumeLine s, subLastLine s)
                                                   (stSubs st) }
            _ -> pure st

    -- The citations a rule makes from outside the boxes it closes.
    outerCitations :: Justification -> [Int]
    outerCitations j =
      case j of
        CP _ _           -> []
        RAA _ _          -> []
        OrElim d _ _ _ _ -> [d]
        ExistsElim m _ _ -> [m]
        _                -> citedLines j

    ruleFor :: Int -> Justification -> M.Map Int SubRef
            -> Either TranslationError FitchRule
    ruleFor n j subs =
      case j of
        CP a _             -> FCP  <$> refFor a
        RAA a _            -> FRAA <$> refFor a
        ExistsElim m a _   -> FExistsE m <$> refFor a
        OrElim d a1 _ a2 _ -> FOrE d <$> refFor a1 <*> refFor a2
        _                  -> plainRule j
      where
        refFor a =
          case M.lookup a subs of
            Nothing -> Left (UnknownAssumption n a)
            Just rf -> Right rf

    plainRule :: Justification -> Either TranslationError FitchRule
    plainRule j =
      case j of
        Assumption    -> pure FAssume
        MP m k        -> pure (FMP m k)
        MT m k        -> pure (FMT m k)
        DN m          -> pure (FDN m)
        AndIntro m k  -> pure (FAndI m k)
        AndElim m     -> pure (FAndE m)
        OrIntro m     -> pure (FOrI m)
        ForallElim m  -> pure (FForallE m)
        ForallIntro m -> pure (FForallI m)
        ExistsIntro m -> pure (FExistsI m)
        EqIntro       -> pure FEqI
        EqElim m k    -> pure (FEqE m k)
        LEM           -> pure FLEM
        PropTaut ms   -> pure (FPropTaut ms)
        IffIntro m k  -> pure (FIffI m k)
        IffElim m k   -> pure (FIffE m k)
        QN m          -> pure (FQN m)
        CP _ _        -> Left (Internal "CP reached plainRule")
        RAA _ _       -> Left (Internal "RAA reached plainRule")
        OrElim{}      -> Left (Internal "OrElim reached plainRule")
        ExistsElim{}  -> Left (Internal "ExistsElim reached plainRule")

    -- A cited line is available iff every box it was written inside is still
    -- open. Comparing placements, not dependency sets, is the point.
    reachable :: Int -> S.Set Int -> Placement -> Int
              -> Either TranslationError ()
    reachable n scope placed cited
      | not (cited `S.member` known) = Left (MissingLine cited)
      | otherwise =
          case M.lookup cited placed of
            Nothing  -> Left (MissingLine cited)
            Just box ->
              case sort (S.toList (box `S.difference` scope)) of
                []      -> Right ()
                (a : _) -> Left (OutOfScope n cited a)

--------------------------------------------------------------------------------
-- The derivation tree, and the complete translation
--------------------------------------------------------------------------------
--
-- A Lemmon proof is a directed acyclic graph: a line cited by two later lines
-- is shared between them. A Fitch proof is a tree: every line sits in exactly
-- one box and is visible only to what that box contains. Unfolding the DAG
-- into a tree is therefore precisely the step that turns sharing into
-- duplication -- and it is also what makes both obstructions disappear.
--
-- In a tree, a discharge closes exactly the box its own subderivation opened,
-- so nesting is automatic and there is no discharge order to get wrong. And
-- nothing is ever cited from a sibling branch, so no line can be stranded in
-- a box that has closed. The price is that a line used twice is derived
-- twice, and in the worst case that is exponential.
--
-- Hence the two paths. The direct translation is tried first: it is exact,
-- it preserves line numbers, and on every real proof measured so far it
-- succeeds. Only when it refuses do we unfold, which costs length and
-- renumbering but always works.

-- | A natural deduction derivation. Assumptions are leaves, labelled with the
-- Lemmon line that introduced them; the rule that discharges one names it.
data Deriv = Deriv
  { dForm :: PredFormula
  , dRule :: DRule
  } deriving (Show, Eq)

data DRule
  = DAssume Int                     -- ^ discharged by an ancestor
  | DPremise Int                    -- ^ never discharged
  | DMP Deriv Deriv
  | DMT Deriv Deriv
  | DDN Deriv
  | DCP Int PredFormula Deriv       -- ^ discharges the named assumption
  | DAndI Deriv Deriv
  | DAndE Deriv
  | DOrI Deriv
  | DOrE Deriv Int PredFormula Deriv Int PredFormula Deriv
  | DRAA Int PredFormula Deriv
  | DForallE Deriv
  | DForallI Deriv
  | DExistsI Deriv
  | DExistsE Deriv Int PredFormula Deriv
  | DEqI
  | DEqE Deriv Deriv
  | DLEM
  | DPropTaut [Deriv]
  | DIffI Deriv Deriv
  | DIffE Deriv Deriv
  | DQN Deriv
  deriving (Show, Eq)

-- | Unfold a Lemmon proof into a derivation tree, rooted at its last line.
--
-- Lines that do not contribute to the conclusion are dropped: they are not
-- part of the derivation of it. The resulting Fitch proof establishes the
-- same formula from the same premises, or fewer.
toDerivation :: Proof -> Either TranslationError Deriv
toDerivation prf =
  case reverse prf of
    []      -> Left (Internal "cannot translate an empty proof")
    (l : _) -> build (lineNumber l)
  where
    byNum = M.fromList [ (lineNumber l, l) | l <- prf ]

    boxed :: S.Set Int
    boxed = S.fromList
      [ a
      | l <- prf
      , a <- case justification l of
               CP a' _            -> [a']
               RAA a' _           -> [a']
               ExistsElim _ a' _  -> [a']
               OrElim _ a1 _ a2 _ -> [a1, a2]
               _                  -> []
      ]

    formOf n =
      case M.lookup n byNum of
        Nothing -> Left (MissingLine n)
        Just l  -> Right (formula l)

    build n =
      case M.lookup n byNum of
        Nothing -> Left (MissingLine n)
        Just l  -> do
          let f = formula l
              node r = Deriv f r
          case justification l of
            Assumption
              | n `S.member` boxed -> pure (node (DAssume n))
              | otherwise          -> pure (node (DPremise n))
            MP m k        -> node <$> (DMP   <$> build m <*> build k)
            MT m k        -> node <$> (DMT   <$> build m <*> build k)
            DN m          -> node <$> (DDN   <$> build m)
            AndIntro m k  -> node <$> (DAndI <$> build m <*> build k)
            AndElim m     -> node <$> (DAndE <$> build m)
            OrIntro m     -> node <$> (DOrI  <$> build m)
            ForallElim m  -> node <$> (DForallE  <$> build m)
            ForallIntro m -> node <$> (DForallI  <$> build m)
            ExistsIntro m -> node <$> (DExistsI  <$> build m)
            EqIntro       -> pure (node DEqI)
            EqElim m k    -> node <$> (DEqE  <$> build m <*> build k)
            LEM           -> pure (node DLEM)
            PropTaut ms   -> node <$> (DPropTaut <$> mapM build ms)
            IffIntro m k  -> node <$> (DIffI <$> build m <*> build k)
            IffElim m k   -> node <$> (DIffE <$> build m <*> build k)
            QN m          -> node <$> (DQN   <$> build m)
            CP a c        -> do af <- formOf a
                                cd <- build c
                                pure (node (DCP a af cd))
            RAA a c       -> do af <- formOf a
                                cd <- build c
                                pure (node (DRAA a af cd))
            ExistsElim m a c -> do md <- build m
                                   af <- formOf a
                                   cd <- build c
                                   pure (node (DExistsE md a af cd))
            OrElim d a1 c1 a2 c2 -> do dd  <- build d
                                       f1  <- formOf a1
                                       c1d <- build c1
                                       f2  <- formOf a2
                                       c2d <- build c2
                                       pure (node (DOrE dd a1 f1 c1d a2 f2 c2d))

-- | Every premise the tree rests on, keyed by the line that introduced it.
premisesOf :: Deriv -> M.Map Int PredFormula
premisesOf (Deriv f r) =
  case r of
    DPremise i -> M.singleton i f
    DAssume _  -> M.empty
    DEqI       -> M.empty
    DLEM       -> M.empty
    DDN a      -> premisesOf a
    DAndE a    -> premisesOf a
    DOrI a     -> premisesOf a
    DForallE a -> premisesOf a
    DForallI a -> premisesOf a
    DExistsI a -> premisesOf a
    DQN a      -> premisesOf a
    DMP a b    -> premisesOf a `M.union` premisesOf b
    DMT a b    -> premisesOf a `M.union` premisesOf b
    DAndI a b  -> premisesOf a `M.union` premisesOf b
    DEqE a b   -> premisesOf a `M.union` premisesOf b
    DIffI a b  -> premisesOf a `M.union` premisesOf b
    DIffE a b  -> premisesOf a `M.union` premisesOf b
    DPropTaut ds        -> M.unions (map premisesOf ds)
    DCP _ _ d           -> premisesOf d
    DRAA _ _ d          -> premisesOf d
    DExistsE d _ _ b    -> premisesOf d `M.union` premisesOf b
    DOrE d _ _ b1 _ _ b2 ->
      M.unions [premisesOf d, premisesOf b1, premisesOf b2]

-- | Rename one constant throughout a formula.
renameConst :: String -> String -> PredFormula -> PredFormula
renameConst old new = go
  where
    t (Const c) | c == old = Const new
    t x                    = x
    go (Predicate p ts) = Predicate p (map t ts)
    go (Boolean b)      = Boolean b
    go (Not p)          = Not (go p)
    go (And p q)        = And (go p) (go q)
    go (Or p q)         = Or (go p) (go q)
    go (Implies p q)    = Implies (go p) (go q)
    go (Iff p q)        = Iff (go p) (go q)
    go (ForAll x p)     = ForAll x (go p)
    go (Exists x p)     = Exists x (go p)

-- | Rename one constant throughout a derivation, formulas carried by
-- discharging rules included.
renameInDeriv :: String -> String -> Deriv -> Deriv
renameInDeriv old new = goD
  where
    rf = renameConst old new
    goD (Deriv f r) = Deriv (rf f) (goR r)
    goR r = case r of
      DAssume i    -> DAssume i
      DPremise i   -> DPremise i
      DEqI         -> DEqI
      DLEM         -> DLEM
      DDN a        -> DDN (goD a)
      DAndE a      -> DAndE (goD a)
      DOrI a       -> DOrI (goD a)
      DForallE a   -> DForallE (goD a)
      DForallI a   -> DForallI (goD a)
      DExistsI a   -> DExistsI (goD a)
      DQN a        -> DQN (goD a)
      DMP a b      -> DMP (goD a) (goD b)
      DMT a b      -> DMT (goD a) (goD b)
      DAndI a b    -> DAndI (goD a) (goD b)
      DEqE a b     -> DEqE (goD a) (goD b)
      DIffI a b    -> DIffI (goD a) (goD b)
      DIffE a b    -> DIffE (goD a) (goD b)
      DPropTaut ds -> DPropTaut (map goD ds)
      DCP i af d   -> DCP i (rf af) (goD d)
      DRAA i af d  -> DRAA i (rf af) (goD d)
      DExistsE d i af b -> DExistsE (goD d) i (rf af) (goD b)
      DOrE d i1 f1 b1 i2 f2 b2 ->
        DOrE (goD d) i1 (rf f1) (goD b1) i2 (rf f2) (goD b2)

-- | Every formula occurring anywhere in a derivation.
derivFormulas :: Deriv -> [PredFormula]
derivFormulas (Deriv f r) = f : case r of
  DAssume _    -> []
  DPremise _   -> []
  DEqI         -> []
  DLEM         -> []
  DDN a        -> derivFormulas a
  DAndE a      -> derivFormulas a
  DOrI a       -> derivFormulas a
  DForallE a   -> derivFormulas a
  DForallI a   -> derivFormulas a
  DExistsI a   -> derivFormulas a
  DQN a        -> derivFormulas a
  DMP a b      -> derivFormulas a ++ derivFormulas b
  DMT a b      -> derivFormulas a ++ derivFormulas b
  DAndI a b    -> derivFormulas a ++ derivFormulas b
  DEqE a b     -> derivFormulas a ++ derivFormulas b
  DIffI a b    -> derivFormulas a ++ derivFormulas b
  DIffE a b    -> derivFormulas a ++ derivFormulas b
  DPropTaut ds -> concatMap derivFormulas ds
  DCP _ af d   -> af : derivFormulas d
  DRAA _ af d  -> af : derivFormulas d
  DExistsE d _ af b -> af : derivFormulas d ++ derivFormulas b
  DOrE d _ f1 b1 _ f2 b2 ->
    f1 : f2 : concatMap derivFormulas [d, b1, b2]

constsInDeriv :: Deriv -> S.Set String
constsInDeriv = S.unions . map constsInFormula . derivFormulas

-- | A constant occurring nowhere yet. Single letters first, so that the
-- renamed proof still reads like a proof.
freshConst :: S.Set String -> String
freshConst used = head [ c | c <- candidates, not (c `S.member` used) ]
  where
    candidates = map (: []) ['a' .. 'z']
              ++ [ c : show i | i <- [(1 :: Int) ..], c <- ['a' .. 'z'] ]

data LinSt = LinSt
  { lsNext  :: Int                -- ^ next free line number
  , lsEnv   :: M.Map Int Int      -- ^ assumption or premise id to its line
  , lsScope :: [PredFormula]      -- ^ assumptions of the enclosing subproofs
  , lsUsed  :: S.Set String       -- ^ every constant spoken for
  }

-- | Lay a derivation tree out as a Fitch proof.
--
-- Premises come first, at the top level, each written once however often it
-- is used. Everything else is emitted in the order Fitch requires: the
-- subderivations a rule needs, then the line that applies it.
derivationToFitch :: Deriv -> FitchProof
derivationToFitch d =
  let pm    = premisesOf d
      ids   = M.keys pm
      env0  = M.fromList (zip ids [1 ..])
      tops  = [ FLine (env0 M.! i) (pm M.! i) FPremise | i <- ids ]
      st0   = LinSt { lsNext  = length ids + 1
                    , lsEnv   = env0
                    , lsScope = []
                    , lsUsed  = constsInDeriv d }
      (_, _, body) = emit st0 d
  in tops ++ body

fresh :: LinSt -> (LinSt, Int)
fresh st = (st { lsNext = lsNext st + 1 }, lsNext st)

-- | Emit a derivation, returning the line its conclusion ended up on.
emit :: LinSt -> Deriv -> (LinSt, Int, [FitchItem])
emit st (Deriv f r) =
  case r of
    DPremise i -> (st, M.findWithDefault 0 i (lsEnv st), [])
    DAssume  i -> (st, M.findWithDefault 0 i (lsEnv st), [])
    DEqI       -> leaf FEqI
    DLEM       -> leaf FLEM
    DDN a      -> un a FDN
    DAndE a    -> un a FAndE
    DOrI a     -> un a FOrI
    DForallE a -> un a FForallE
    -- The one rule whose side condition is about assumptions rather than
    -- formulas. Lemmon tests arbitrariness against the dependency set, Fitch
    -- against scope; where a name generalised upon occurs in an assumption
    -- that encloses this line without being depended on, the Fitch condition
    -- fails though the Lemmon one held. The repair is local: rename the
    -- subderivation to a name occurring nowhere. Its open assumptions do not
    -- contain the old name -- that is what the Lemmon condition says -- so
    -- they are untouched, and the conclusion does not contain it either,
    -- since abstraction removes every occurrence.
    DForallI a ->
      let (stR, a') = fixEigen st f a
          (st1, n1, i1) = emit stR a'
          (st2, n)      = fresh st1
      in (st2, n, i1 ++ [FLine n f (FForallI n1)])
    DExistsI a -> un a FExistsI
    DQN a      -> un a FQN
    DMP a b    -> bin a b FMP
    DMT a b    -> bin a b FMT
    DAndI a b  -> bin a b FAndI
    DEqE a b   -> bin a b FEqE
    DIffI a b  -> bin a b FIffI
    DIffE a b  -> bin a b FIffE

    DPropTaut ds ->
      let (st1, ns, iss) = emitMany st ds
          (st2, n)       = fresh st1
      in (st2, n, concat iss ++ [FLine n f (FPropTaut ns)])

    DCP a af body  -> boxRule a af body FCP
    DRAA a af body -> boxRule a af body FRAA

    DExistsE d0 a af body ->
      let (st1, n0, i0)  = emit st d0
          (st2, sr, isb) = mkBox st1 a af body
          (st3, n)       = fresh st2
      in (st3, n, i0 ++ isb ++ [FLine n f (FExistsE n0 sr)])

    DOrE d0 a1 f1 b1 a2 f2 b2 ->
      let (st1, n0, i0)  = emit st d0
          (st2, s1, is1) = mkBox st1 a1 f1 b1
          (st3, s2, is2) = mkBox st2 a2 f2 b2
          (st4, n)       = fresh st3
      in (st4, n, i0 ++ is1 ++ is2 ++ [FLine n f (FOrE n0 s1 s2)])
  where
    leaf rule =
      let (st1, n) = fresh st in (st1, n, [FLine n f rule])

    un a mk =
      let (st1, n1, i1) = emit st a
          (st2, n)      = fresh st1
      in (st2, n, i1 ++ [FLine n f (mk n1)])

    bin a b mk =
      let (st1, n1, i1) = emit st a
          (st2, n2, i2) = emit st1 b
          (st3, n)      = fresh st2
      in (st3, n, i1 ++ i2 ++ [FLine n f (mk n1 n2)])

    boxRule a af body mk =
      let (st1, sr, isb) = mkBox st a af body
          (st2, n)       = fresh st1
      in (st2, n, isb ++ [FLine n f (mk sr)])

-- | Rename away any name generalised upon that occurs in an enclosing
-- assumption. Returns the state with the fresh names reserved.
fixEigen :: LinSt -> PredFormula -> Deriv -> (LinSt, Deriv)
fixEigen st goal d = foldl step (st, d) bad
  where
    -- Abstraction replaces every occurrence, so a name that was generalised
    -- cannot survive into the goal: the difference is exactly the
    -- eigenvariables.
    eig = constsInFormula (dForm d) `S.difference` constsInFormula goal
    bad = [ c | c <- S.toList eig
              , any (S.member c . constsInFormula) (lsScope st) ]
    step (s, dd) c =
      let nu = freshConst (lsUsed s)
      in (s { lsUsed = S.insert nu (lsUsed s) }, renameInDeriv c nu dd)

emitMany :: LinSt -> [Deriv] -> (LinSt, [Int], [[FitchItem]])
emitMany st []       = (st, [], [])
emitMany st (d : ds) =
  let (st1, n, i)   = emit st d
      (st2, ns, is) = emitMany st1 ds
  in (st2, n : ns, i : is)

-- | Build one subproof: allocate its assumption line, bind the assumption so
-- that uses inside refer to it, then emit the body.
--
-- If the body concludes with a line from outside the box -- a premise, or an
-- outer assumption -- the box would contain nothing and cite a line beyond
-- its own edge. That is what reiteration is for.
mkBox :: LinSt -> Int -> PredFormula -> Deriv -> (LinSt, SubRef, [FitchItem])
mkBox st a af body =
  let (st1, aLine)     = fresh st
      st2              = st1 { lsEnv   = M.insert a aLine (lsEnv st1)
                             , lsScope = af : lsScope st1 }
      (st3', nc, items) = emit st2 body
      -- Leaving the subproof: its assumption is no longer in scope.
      st3               = st3' { lsScope = lsScope st1 }
  in if null items && nc /= aLine
       then let (st4, rl) = fresh st3
                items'    = [FLine rl (dForm body) (FReit nc)]
            in (st4, (aLine, rl), [FSub (Subproof aLine af items')])
       else (st3, (aLine, nc), [FSub (Subproof aLine af items)])

--------------------------------------------------------------------------------
-- The complete translation
--------------------------------------------------------------------------------

-- | Which path produced a translation.
data Route
  = Direct   -- ^ line for line; numbering and structure preserved
  | ViaTree  -- ^ unfolded through a derivation tree; renumbered, and lines
             --   used more than once are derived more than once
  deriving (Show, Eq)

-- | Translate any valid Lemmon proof into Fitch.
--
-- The direct translation is tried first because it is exact. When it refuses,
-- the proof is unfolded into a derivation tree and laid out from that, which
-- always succeeds at the cost of length.
lemmonToFitch :: Proof -> Either TranslationError (Route, FitchProof)
lemmonToFitch prf =
  case lemmonToFitchDirect prf of
    Right fp -> Right (Direct, fp)
    Left _   -> do
      d <- toDerivation prf
      pure (ViaTree, derivationToFitch d)
