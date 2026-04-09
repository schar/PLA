{-# OPTIONS_GHC -Wno-orphans #-}
{- HLINT ignore "Use tuple-section" -}

module Main where

import qualified Data.Map as M
import qualified Data.Set as S
import System.Exit (exitFailure)
import Test.QuickCheck

import EEDPL

-- Show instances for QuickCheck counterexample reporting.
-- Form and State contain functions, so we show structure only.

instance Show Form where
  show (Rel _ vs) = "Rel <pred> " ++ show vs
  show (Ex v)     = "Ex " ++ show v
  show (Not p)    = "Not (" ++ show p ++ ")"
  show (And p q)  = "And (" ++ show p ++ ") (" ++ show q ++ ")"

instance Show State where
  show s = "State " ++ show (dom s) ++ " <info>"

-- Generators

-- | Pick from a small pool of variables to keep sat tractable
-- (2 vars => 100^2 = 10,000 assignments).
allVars :: [Var]
allVars = [Var 'x', Var 'y']

-- | Extended variable pool (3 vars => 100^3 = 10^6 assignments).
extVars :: [Var]
extVars = [Var 'x', Var 'y', Var 'z']

genVar :: Gen Var
genVar = elements allVars

-- | Deterministic relation predicates.
genRel :: Int -> Gen ([E] -> Bool)
genRel n = elements preds
  where
    preds =
      [ \es -> length es == n && even (sum es)
      , \es -> length es == n && all (> 50) es
      , \es -> length es == n && head es > last es
      , const True
      , const False
      ]

-- | Generate a formula up to a given depth.
genForm :: Int -> Gen Form
genForm 0 = oneof
  [ do arity <- choose (1, 2)
       vs <- vectorOf arity genVar
       r <- genRel arity
       pure (Rel r vs)
  , Ex <$> genVar
  ]
genForm n = frequency
  [ (3, do arity <- choose (1, 2)
           vs <- vectorOf arity genVar
           r <- genRel arity
           pure (Rel r vs))
  , (2, Ex <$> genVar)
  , (2, Not <$> genForm (n - 1))
  , (3, And <$> genForm (n `div` 2) <*> genForm (n `div` 2))
  ]

-- | 'Arbitrary' instance exists for 'shrink' only. All properties use
-- specific generators ('genWellFormed', 'genWellFormedMerge', etc.) via
-- 'forAll'; 'arbitrary' here is never called directly.
instance Arbitrary Form where
  arbitrary = sized $ \s -> genForm (min s 3)
  shrink (Not p) = p : [Not p' | p' <- shrink p]
  shrink (And p q) = [p, q] ++ [And p' q | p' <- shrink p]
                            ++ [And p q' | q' <- shrink q]
  shrink _ = []

-- | Generate a well-formed formula by threading available variables.
-- @avail@ tracks variables in scope (free or previously introduced).
-- @introduced@ tracks variables introduced by Ex so far (to prevent
-- double-introduction).
genWellFormedForm :: Int -> S.Set Var -> S.Set Var -> Gen Form
genWellFormedForm 0 avail introduced = frequency $
  [ (2, do v <- elements fresh; pure (Ex v))
    | let fresh = filter (`S.notMember` introduced) allVars
    , not (null fresh)
  ] ++
  [ (3, do arity <- choose (1, 2)
           vs <- vectorOf arity (elements (S.toList avail))
           r <- genRel arity
           pure (Rel r vs))
    | not (S.null avail)
  ] ++
  -- Fallback: a trivial Rel when no variables are available.
  [ (1, pure (Rel (const True) []))
    | let fresh = filter (`S.notMember` introduced) allVars
    , null fresh, S.null avail
  ]
genWellFormedForm n avail introduced = frequency $
  [ (2, do v <- elements fresh; pure (Ex v))
    | let fresh = filter (`S.notMember` introduced) allVars
    , not (null fresh)
  ] ++
  [ (3, do arity <- choose (1, 2)
           vs <- vectorOf arity (elements (S.toList avail))
           r <- genRel arity
           pure (Rel r vs))
    | not (S.null avail)
  ] ++
  [ (2, Not <$> genWellFormedForm (n - 1) avail introduced)
  , (3, do p <- genWellFormedForm (n `div` 2) avail introduced
           let avail' = avail `S.union` ivSyn p
               introduced' = introduced `S.union` ivSyn p
           q <- genWellFormedForm (n `div` 2) avail' introduced'
           pure (And p q))
  ]

genWellFormed :: Gen Form
genWellFormed = sized $ \s -> genWellFormedForm (min s 3) S.empty S.empty

-- | Generate a well-formed formula compatible with @evalStatic'@.
-- In @evalStatic'@, @And@ is interpreted via @merge@, which restricts the
-- left operand's assignment to its own domain. So @Rel@ variables in the
-- left subtree must be introduced (by @Ex@) within that subtree. The right
-- subtree receives the full assignment and can reference variables introduced
-- on the left. We track @own@ (variables introduced in the current subtree)
-- separately from @avail@ (all variables reachable, for the right operand).
--
-- Note: the @own@ restriction applies equally inside @Not@. Although
-- @evalStatic' (Not p) = complement (reduceBy (dom p) p)@ doesn't use
-- @merge@, it preserves the free-variable partiality of @Rel@'s info
-- function. A @Not (Rel [x] ...)@ still requires @x@ in the assignment,
-- and will crash when placed as the left operand of a @merge@.
--
-- @vars@ is the full variable pool (e.g. @allVars@ or @extVars@).
genMergeForm :: [Var] -> Int -> S.Set Var -> S.Set Var -> Gen Form
genMergeForm vars 0 own introduced = frequency $
  [ (2, do v <- elements fresh; pure (Ex v))
    | let fresh = filter (`S.notMember` introduced) vars
    , not (null fresh)
  ] ++
  [ (3, do arity <- choose (1, 2)
           vs <- vectorOf arity (elements (S.toList own))
           r <- genRel arity
           pure (Rel r vs))
    | not (S.null own)
  ] ++
  -- Fallback: a trivial Rel with no variable references.
  [ (1, pure (Rel (const True) []))
    | let fresh = filter (`S.notMember` introduced) vars
    , null fresh, S.null own
  ]
genMergeForm vars n own introduced = frequency $
  [ (2, do v <- elements fresh; pure (Ex v))
    | let fresh = filter (`S.notMember` introduced) vars
    , not (null fresh)
  ] ++
  [ (3, do arity <- choose (1, 2)
           vs <- vectorOf arity (elements (S.toList own))
           r <- genRel arity
           pure (Rel r vs))
    | not (S.null own)
  ] ++
  [ (2, Not <$> genMergeForm vars (n - 1) own introduced)
  , (3, do -- left subtree: Rel can only use vars introduced within it
           p <- genMergeForm vars (n `div` 2) S.empty introduced
           let introduced' = introduced `S.union` ivSyn p
           -- right subtree: gets full assignment, Rel can use own + left's vars
           q <- genMergeForm vars (n `div` 2) (own `S.union` ivSyn p) introduced'
           pure (And p q))
  ]

genWellFormedMerge :: Gen Form
genWellFormedMerge = sized $ \s -> genMergeForm allVars (min s 3) S.empty S.empty

-- | Merge-compatible formulas over 3 variables.
genWellFormedMerge3 :: Gen Form
genWellFormedMerge3 = sized $ \s -> genMergeForm extVars (min s 3) S.empty S.empty

-- | Merge-compatible formulas with free variables from @free@.
-- Used for testing the merge equivalence from a non-trivial state.
-- Passing @free@ as both @own@ and @introduced@ lets Rel reference those
-- variables while preventing Ex from re-introducing them.
genMergeFormOver :: S.Set Var -> Gen Form
genMergeFormOver free = sized $ \s -> genMergeForm allVars (min s 3) free free

-- | Generate a state over a small domain with a deterministic,
-- hash-based info content.
genState :: Gen State
genState = do
  vs <- sublistOf allVars
  let d = S.fromList vs
  threshold <- choose (1 :: Int, 200)
  pure $ State d (\g -> hashG (M.restrictKeys g d) `mod` 200 < threshold)
  where
    hashG g = sum [fromEnum c * v | (Var c, v) <- M.toList g]

-- | Generate a state whose domain includes @required@ but excludes @excluded@.
genStateOver :: Domain -> Domain -> Gen State
genStateOver required excluded = do
  let eligible = filter (\v -> v `S.notMember` required && v `S.notMember` excluded) allVars
  extra <- sublistOf eligible
  let d = required `S.union` S.fromList extra
  threshold <- choose (1 :: Int, 200)
  pure $ State d (\g -> hashG (M.restrictKeys g d) `mod` 200 < threshold)
  where
    hashG g = sum [fromEnum c * v | (Var c, v) <- M.toList g]

instance Arbitrary State where
  arbitrary = genState

-- | Generate a pair of states with disjoint domains.
genDisjointPair :: Gen (State, State)
genDisjointPair = do
  -- Partition allVars randomly into two disjoint sets.
  partition <- mapM (\v -> (\b -> (v, b)) <$> elements [True, False]) allVars
  let vs1 = S.fromList [v | (v, True)  <- partition]
      vs2 = S.fromList [v | (v, False) <- partition]
  t1 <- choose (1 :: Int, 200)
  t2 <- choose (1 :: Int, 200)
  let hash g = sum [fromEnum c * v | (Var c, v) <- M.toList g]
  pure ( State vs1 (\g -> hash (M.restrictKeys g vs1) `mod` 200 < t1)
       , State vs2 (\g -> hash (M.restrictKeys g vs2) `mod` 200 < t2)
       )

-- | Generate a triple of states with mutually disjoint domains.
genDisjointTriple :: Gen (State, State, State)
genDisjointTriple = do
  let pool = allVars ++ [Var 'z']
  -- Assign each variable to one of three buckets.
  assignment <- mapM (\v -> (\b -> (v, b)) <$> elements [0 :: Int, 1, 2]) pool
  let vs i = S.fromList [v | (v, b) <- assignment, b == i]
  t1 <- choose (1 :: Int, 200)
  t2 <- choose (1 :: Int, 200)
  t3 <- choose (1 :: Int, 200)
  let hash g = sum [fromEnum c * v | (Var c, v) <- M.toList g]
      d0 = vs 0; d1 = vs 1; d2 = vs 2
  pure ( State d0 (\g -> hash (M.restrictKeys g d0) `mod` 200 < t1)
       , State d1 (\g -> hash (M.restrictKeys g d1) `mod` 200 < t2)
       , State d2 (\g -> hash (M.restrictKeys g d2) `mod` 200 < t3)
       )

-- Comparison helper: two states are equivalent iff they have
-- the same domain and the same satisfying assignments.

stateEq :: State -> State -> Bool
stateEq s t =
  dom s == dom t && S.fromList (sat s) == S.fromList (sat t)

-- Properties

-- | Strawson equivalence (Dekker 1996):
-- When evalDyn phi s is defined, evalDyn phi s == s /\ evalStatic phi.
prop_strawson :: Property
prop_strawson = forAll genWellFormed $ \phi ->
  let s = initState
   in case evalDyn phi s of
        Right dynState -> label (formShape phi) $
          property $ stateEq dynState (s /\ evalStatic phi)
        Left _         -> property Discard

-- | Merge equivalence (2 variables):
-- When evalDyn phi s is defined, evalDyn phi s == s `merge` evalStatic' phi.
prop_merge :: Property
prop_merge = forAll genWellFormedMerge $ \phi ->
  let s = initState
   in case evalDyn phi s of
        Right dynState -> label (formShape phi) $
          property $ stateEq dynState (s `merge` evalStatic' phi)
        Left _ -> property Discard

-- | Merge equivalence (3 variables).
-- Wider variable space to stress-test the unproved theorem.
prop_mergeExt :: Property
prop_mergeExt = forAll genWellFormedMerge3 $ \phi ->
  let s = initState
   in case evalDyn phi s of
        Right dynState -> label (formShape phi) $
          property $ stateEq dynState (s `merge` evalStatic' phi)
        Left _ -> property Discard

-- | Merge equivalence from a non-trivial state.
-- evalDyn phi s == s `merge` evalStatic' phi, where s provides the free
-- variables. The formula is generated with own = dom s and introduced = dom s,
-- so Rel can reference s's variables and Ex won't re-introduce them,
-- guaranteeing dom s and dom (evalStatic' phi) are disjoint.
prop_mergeState :: Property
prop_mergeState = forAll genState $ \s ->
  forAll (genMergeFormOver (dom s)) $ \phi ->
    case evalDyn phi s of
      Right dynState -> label (formShape phi) $
        property $ stateEq dynState (s `merge` evalStatic' phi)
      Left _ -> property Discard

-- | Strawson equivalence from a non-trivial state.
-- evalDyn phi s == s /\ evalStatic phi, when defined.
-- We generate s to contain exactly phi's free variables but not its
-- introduced variables, so evalDyn won't fail on novelty or familiarity.
prop_strawsonState :: Property
prop_strawsonState = forAll genWellFormed $ \phi ->
  forAll (genStateOver (fvSyn phi) (ivSyn phi)) $ \s ->
    case evalDyn phi s of
      Right dynState -> property $ stateEq dynState (s /\ evalStatic phi)
      Left _         -> property Discard

-- | Complement is involutive: complement (complement s) == s.
prop_complementInvolutive :: State -> Property
prop_complementInvolutive s =
  property $ stateEq (complement (complement s)) s

-- | Meet is idempotent: s /\ s == s.
prop_meetIdem :: State -> Property
prop_meetIdem s = property $ stateEq (s /\ s) s

-- | Join is idempotent: s \/ s == s.
prop_joinIdem :: State -> Property
prop_joinIdem s = property $ stateEq (s \/ s) s

-- | Meet is commutative: s /\ t == t /\ s.
prop_meetComm :: State -> State -> Property
prop_meetComm s t = property $ stateEq (s /\ t) (t /\ s)

-- | Join is commutative: s \/ t == t \/ s.
prop_joinComm :: State -> State -> Property
prop_joinComm s t = property $ stateEq (s \/ t) (t \/ s)

-- | top d is the identity for meet: s /\ top d == s (when domains agree).
prop_meetTop :: State -> Property
prop_meetTop s =
  property $ stateEq (s /\ top (dom s)) s

-- | bottom d is the identity for join: s \/ bottom d == s (when domains agree).
prop_joinBottom :: State -> Property
prop_joinBottom s =
  property $ stateEq (s \/ bottom (dom s)) s

-- | extendBy then reduceBy is the identity (round-trip).
prop_extendReduceRoundTrip :: State -> Property
prop_extendReduceRoundTrip s =
  forAll (elements (filter (\v -> v `S.notMember` dom s) (allVars ++ [Var 'z']))) $ \v ->
    let extra = S.singleton v
     in stateEq (reduceBy extra (extendBy extra s)) s

-- | Left identity for merge: initState `merge` s == s.
prop_mergeLeftId :: State -> Property
prop_mergeLeftId s =
  property $ stateEq (initState `merge` s) s

-- | Right identity for merge: s `merge` initState == s.
prop_mergeRightId :: State -> Property
prop_mergeRightId s =
  property $ stateEq (s `merge` initState) s

-- | Associativity of merge (given mutually disjoint domains):
-- (s `merge` t) `merge` u == s `merge` (t `merge` u)
prop_mergeAssoc :: Property
prop_mergeAssoc = forAll genDisjointTriple $ \(s, t, u) ->
  stateEq ((s `merge` t) `merge` u) (s `merge` (t `merge` u))

-- | Merge coincides with meet when domains are disjoint:
-- s `merge` t == s /\ extendBy (dom s) t
prop_mergeMeet :: Property
prop_mergeMeet = forAll genDisjointPair $ \(s, t) ->
  stateEq (s `merge` t) (s /\ extendBy (dom s) t)

-- | fvSyn agrees with fvSem on well-formed formulas.
prop_fvSynSem :: Property
prop_fvSynSem = forAll genWellFormed $ \phi ->
  let vars = S.toList $ fvSyn phi `S.union` ivSyn phi
   in label (formShape phi) $
        fvSem vars (evalDyn phi) == fvSyn phi

-- | Classify formula shape for QuickCheck label output.
formShape :: Form -> String
formShape (Rel _ vs) = "Rel/" ++ show (length vs)
formShape (Ex _)     = "Ex"
formShape (Not p)    = "Not(" ++ formShape p ++ ")"
formShape (And p q)  = "And(" ++ formShape p ++ "," ++ formShape q ++ ")"

-- | test0 from the module.
prop_test0 :: Property
prop_test0 = property test0

-- | test1 from the module.
prop_test1 :: Property
prop_test1 = property test1

-- Run all tests

check :: String -> Int -> Property -> IO Bool
check name n p = do
  putStrLn $ "\n-- " ++ name ++ " --"
  r <- quickCheckWithResult (stdArgs { maxSuccess = n, chatty = True }) p
  pure $ case r of
    Success {} -> True
    _          -> False

main :: IO ()
main = do
  putStrLn "=== EEDPL QuickCheck Test Suite ==="
  results <- sequence
    [ check "Strawson equivalence (from initState)"    200 prop_strawson
    , check "Merge equivalence (2 vars, initState)"    200 prop_merge
    , check "Merge equivalence (3 vars, initState)"     50 prop_mergeExt
    , check "Merge equivalence (from arbitrary state)" 200 prop_mergeState
    , check "Strawson equivalence (from arbitrary state)" 200 prop_strawsonState
    , check "Complement is involutive"                 200 (property prop_complementInvolutive)
    , check "Meet idempotent"                          200 (property prop_meetIdem)
    , check "Join idempotent"                          200 (property prop_joinIdem)
    , check "Meet commutative"                         200 (property prop_meetComm)
    , check "Join commutative"                         200 (property prop_joinComm)
    , check "Meet with top is identity"                200 (property prop_meetTop)
    , check "Join with bottom is identity"             200 (property prop_joinBottom)
    , check "Extend then reduce round-trip"            200 (property prop_extendReduceRoundTrip)
    , check "Merge left identity"                       200 (property prop_mergeLeftId)
    , check "Merge right identity"                      200 (property prop_mergeRightId)
    , check "Merge associativity"                        50 prop_mergeAssoc
    , check "Merge coincides with meet"                 200 prop_mergeMeet
    , check "fvSyn agrees with fvSem"                  200 prop_fvSynSem
    , check "test0 (static vs DPL)"                    100 prop_test0
    , check "test1 (static' vs DPL)"                   100 prop_test1
    ]
  if and results
    then putStrLn "\n=== All tests passed ==="
    else do
      putStrLn $ "\n=== " ++ show (length (filter not results)) ++ " test(s) FAILED ==="
      exitFailure
