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
--   2. Scope is coarser than dependency. Fix a nesting a₁ ⊃ a₂ ⊃ a₃ and put
--      each line as deep as its deepest dependency. A line depending on
--      {a₁, a₃} then sits inside a₂'s box, which is legal — it simply does
--      not use a₂ — but when a₂'s box closes, that line goes out of scope
--      even though it never depended on a₂. In Lemmon it survives a₂'s
--      discharge untouched. Where a proof relies on that survival, no
--      nesting order helps and the line must be *derived twice*, once in
--      each box that needs it.
--
-- The second is the real content of the problem, and it is why the general
-- translation should go through a derivation tree: a Lemmon proof is a DAG,
-- in which a line cited twice is shared, while a Fitch proof is a tree, in
-- which every line lives in one place and is visible only to its
-- descendants. Unfolding the DAG is where duplication becomes forced.
--
-- What is implemented here is the direct, non-duplicating translation: it
-- succeeds on any Lemmon proof whose discharge structure already nests, which
-- covers essentially every textbook proof, and it reports precisely which of
-- the two obstructions it hit when it fails. It does not yet reorder, and it
-- does not duplicate. Both are additions on top of this, not rewrites of it.

module FitchConvert
  ( fitchToLemmon
  , lemmonToFitch
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
lemmonToFitch :: Proof -> Either TranslationError FitchProof
lemmonToFitch prf = reverse <$> go prf (St [] [] M.empty M.empty)
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
          | otherwise ->
              pure (emit n (formula l) FPremise scope st)
        _ -> do
          r <- ruleFor n j (stSubs st)
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
