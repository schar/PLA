{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, TypeFamilies #-}

module EEDPL (module EEDPL, module Shared) where

import Control.Exception (ErrorCall (..), evaluate, try)
import Control.Monad (replicateM)
import Data.Either (isRight)
import Data.List (isPrefixOf, subsequences)
import qualified Data.Map as M
import qualified Data.Set as S
import Shared

-- Basic data and types

-- | The domain of entities is @Int@.
type E = Int

-- | Universe of discourse.
univ :: [E]
univ = [1 .. 100]

-- | Named variables.
newtype Var = Var Char
  deriving (Eq, Ord, Enum, Show)

-- | Partial variable assignments.
type G = M.Map Var E

-- | A State is a domain and an info state. The domain is strict so that a
-- novelty violation in @merge@'s @d <+> d'@ is raised when the state is built,
-- not when its domain happens to be read.
data State = State !Vars (G -> Bool)

-- | Domains are sets of variables.
type Vars = S.Set Var

instance Domain Vars where
  zero = S.empty
  widen = S.union
  narrow = S.intersection
  diff = (S.\\)

instance System State where
  type Dom State = Vars
  dom (State d _) = d
  top d = State d (const True)
  complement (State d f) = State d (not . f)
  extendBy = flip (foldl' addRef)

  -- @M.union@ is left-biased, so @flip M.union@ lets the witness overwrite: total.
  reduceBy = closeWith (flip M.union)
  infoMeet (State d s) (State _ t) = State d (liftA2 (&&) s t)
  infoJoin (State d s) (State _ t) = State d (liftA2 (||) s t)

-- | Add a referent to a state
addRef :: State -> Var -> State
addRef (State d s) v = State (S.insert v d) (s . M.delete v)

-- | Existentially close a domain, one variable at a time: some witness for it,
-- joined to the input by @u@ (the talk's @ij@), satisfies the state.
closeWith :: (G -> G -> G) -> Vars -> State -> State
closeWith u = flip (foldl' close)
  where
    close (State d s) v = State (S.delete v d) (\i -> any (\x -> s $! i `u` M.singleton v x) univ) -- $!: a raising @u@ must fire even if @s@ never reads the join

-- | Delete a referent from a state (existential projection).
delRef :: State -> Var -> State
delRef s v = reduceBy (S.singleton v) s

-- | Disjoint union, raising on overlap: novelty, at domains (in @merge@) and
-- at assignments (under negation, the talk's @ij@).
class DisjointUnion a where
  (<+>) :: a -> a -> a

instance DisjointUnion Vars where
  d <+> e
    | S.disjoint d e = S.union d e
    | otherwise = error ("Novelty violation: " ++ show (S.toList (S.intersection d e)))

instance DisjointUnion G where
  i <+> j
    | M.disjoint i j = M.union i j
    | otherwise = error ("Novelty violation: " ++ show (M.keys (M.intersection i j)))

-- | State merge, given disjoint domains. Analogous to PLA: the left state sees
-- @e@ minus the right state's referents (cf. PLA's @drop n@).
merge :: State -> State -> State
merge (State d s) (State d' t) = State (d <+> d') (\e -> s (M.withoutKeys e d') && t e)

-- | Symmetric / Zeevat merge
mergeSymm :: State -> State -> State
mergeSymm (State d s) (State d' t) = State (S.union d d') (liftA2 (&&) s t)

-- | All total assignments over a domain.
assignments :: Vars -> [G]
assignments d = map (M.fromList . zip vs) (replicateM (length vs) univ)
  where
    vs = S.toList d

-- | Enumerate all satisfying assignments for a state.
sat :: State -> [G]
sat (State d f) = filter f (assignments d)

-- | An alternative perspective on update and context initialization.
-- Materialization of a state involves realizing every partial assignment
-- consistent with it.
satElim :: [Var] -> State -> [G]
satElim vars (State d f) = filter f partials
  where
    partials =
      [ M.fromList (zip sub vals)
        | sub <- subsequences vars,
          d `S.isSubsetOf` S.fromList sub,
          vals <- replicateM (length sub) univ
      ]

-- Formulas and dynamic and static interpretations

-- | First-order formulas with random assignment.
data Form
  = Rel ([E] -> Bool) [Var]
  | Ex Var
  | Not Form
  | And Form Form

-- | Resolve a sequence of variables at an assignment.
resolve :: [Var] -> G -> [E]
resolve vs g = map (g M.!) vs

-- | Standard dynamic evaluation: update a state with a formula. Uses @Either@
-- to facilitate @fvSem@ below.
evalDyn :: Form -> State -> Either String State
evalDyn (Rel r vs) s
  | S.fromList vs `S.isSubsetOf` dom s =
    Right (s @@ State (dom s) (r . resolve vs))
  | otherwise = Left "Un-familiar"
evalDyn (Ex v) s@(State d _)
  | v `S.member` d = Left "Un-novel"
  | otherwise = Right (addRef s v)
evalDyn (Not p) s = (s \\) <$> evalDyn p s
evalDyn (And p q) s = evalDyn p s >>= evalDyn q

-- | Static content of a formula. Indefinites are variables (or vice versa).
evalStatic :: Form -> State
evalStatic (Rel r vs) = State (S.fromList vs) (r . resolve vs)
evalStatic (Ex v) = top (S.singleton v)
evalStatic (Not p) = complement prej
  where
    pSem = evalStatic p
    vars = S.toList (dom pSem)
    prej = bottom (fvSem vars (evalDyn p)) \/ pSem
evalStatic (And p q) = evalStatic p /\ evalStatic q

-- Dekker 1996 proves:
-- When defined: evalDyn phi s == s /\ evalStatic phi (Strawson equivalence)
-- We add: evalDyn phi s == s `merge` evalStatic' phi (equivalence)

-- | Static content of a formula, *with* novelty and familiarity, following
-- @PLA@. It is crucial that a state's info is a partial @G -> Bool@, and so
-- this can't be replicated in @EDPL@. Familiarity is the partiality of
-- @resolve@; novelty that of @<+>@, at domains in @merge@ and at assignments
-- under negation.
evalStatic' :: Form -> State
evalStatic' (Rel r vs) = State zero (r . resolve vs)     -- familiarity from @resolve@
evalStatic' (Ex v) = top (S.singleton v)
evalStatic' (Not p) = let s = evalStatic' p in complement (closeWith (<+>) (dom s) s) -- novelty from @<+>@
evalStatic' (And p q) = evalStatic' p `merge` evalStatic' q -- novelty from @merge@

-- | Static content of a formula, like @evalStatic@ but with only *introduced*
-- variables in a @State@'s @dom@. Allows a more straightforward definition of
-- negation as the complement of the prejacent, and conjunction in terms of
-- symmetric merge. Total, with no novelty or familiarity conditions, and
-- Strawson equivalent to @evalDyn@ via @mergeSymm@.
evalStatic'' :: Form -> State
evalStatic'' (Rel r vs) = State zero (\g -> all (`M.member` g) vs && r (resolve vs g)) -- the guard makes this total; @resolve@ alone is partial
evalStatic'' (Ex v) = top (S.singleton v)
evalStatic'' (Not p) = let s = evalStatic'' p in complement (reduceBy (dom s) s)
evalStatic'' (And p q) = evalStatic'' p `mergeSymm` evalStatic'' q

-- | Free variables, found semantically: the variables common to every domain
-- on which the update is defined. Definedness depends only on the domain, so
-- the probe states carry no assignments.
fvSem :: [Var] -> (State -> Either err State) -> Vars
fvSem vars upd =
  foldr S.intersection (S.fromList vars)
    [d | d <- map S.fromList (subsequences vars), isRight (upd (State d (const False)))]

-- | Syntactically finding free variables.
fvSyn :: Form -> Vars
fvSyn (Rel _ vs) = S.fromList vs
fvSyn (Ex _)     = S.empty
fvSyn (Not p)    = fvSyn p
fvSyn (And p q)  = fvSyn p `S.union` (fvSyn q S.\\ ivSyn p)

-- | Syntactically finding introduced variables.
ivSyn :: Form -> Vars
ivSyn (Rel _ _)  = S.empty
ivSyn (Ex v)     = S.singleton v
ivSyn (Not _)    = S.empty
ivSyn (And p q)  = ivSyn p `S.union` ivSyn q

-- Examples/tests.

gt :: [E] -> Bool
gt [x, y] = x > y
gt _      = error "arity"

lt :: [E] -> Bool
lt [x, y] = x < y
lt _     = error "arity"

big :: [E] -> Bool
big [x] = x > 50
big _   = error "arity"

s0, s1, ex, ey :: Form
-- | There is an @x@ and there is a @y@.
s0 = And (Ex (Var 'x')) (Ex (Var 'y'))
-- | There is no @z@ greater than @x@.
s1 = Not (And (Ex (Var 'z')) (Rel gt [Var 'z', Var 'x']))
-- | Conjoining in anaphoric order.
ex = And s0 s1
-- | Conjoining in cataphoric order.
ey = And s1 s0

-- | There is an @x@; it is big and there is a @y@. The inner left conjunct has
-- a free variable and the right one introduces a referent, so @merge@ must
-- hide only the right conjunct's referents from the left.
ez :: Form
ez = And (Ex (Var 'x')) (And (Rel big [Var 'x']) (Ex (Var 'y')))

-- | There are an @x@ and a @y@, @x > y@, and there is no @x@ less than @y@:
-- the negation reintroduces @x@, violating novelty.
ew :: Form
ew = And (And s0 (Rel gt [Var 'x', Var 'y'])) (Not (And (Ex (Var 'x')) (Rel lt [Var 'x', Var 'y'])))

test0 :: Bool
test0 = Right (sat (evalStatic  ex)) == (sat <$> evalDyn ex initState)

test1 :: Bool
test1 = Right (sat (evalStatic' ex)) == (sat <$> evalDyn ex initState)

-- | @evalDyn@ rejects @ew@ as un-novel, and @evalStatic'@ raises on it, and on
-- the atom-free @∃x ∧ ¬∃x@, where nothing inside the negation reads the
-- joined assignment.
test2 :: IO Bool
test2 = do
  let raises f = either (\(ErrorCall m) -> "Novelty violation" `isPrefixOf` m) (const False) <$> try (evaluate (length (sat (evalStatic' f))))
  a <- raises ew
  b <- raises (And (Ex (Var 'x')) (Not (Ex (Var 'x'))))
  pure (either (== "Un-novel") (const False) (evalDyn ew initState) && a && b)

test3 :: Bool
test3 = Right (sat (evalStatic' ez)) == (sat <$> evalDyn ez initState)

main :: IO ()
main = do
  putStrLn $ "test0 (static  vs DPL): " ++ show test0
  putStrLn $ "test1 (static' vs DPL): " ++ show test1
  test2 >>= \b -> putStrLn ("test2 (novelty on ew): " ++ show b)
  putStrLn $ "test3 (static' vs DPL, ez): " ++ show test3
