{-# LANGUAGE FlexibleInstances, TypeFamilies #-}

module SEDPL (module SEDPL, module Shared) where

-- EDPL over referent systems, after Vermeulen's sequence semantics (1993): a
-- variable points to a stack of values, newest first. Reintroducing a variable pushes a
-- value and shadows the old one instead of clashing, so there is no novelty
-- condition anywhere. Familiarity is still a partial lookup. A domain counts
-- the referents introduced per variable, so the static meaning of a formula
-- is a count and a predicate, as in the talk's ⟨⟨φ⟩⟩, with names.

import Control.Exception (ErrorCall (..), evaluate, try)
import Control.Monad (replicateM)
import Data.List (isPrefixOf)
import qualified Data.Map as M
import Data.Maybe (fromMaybe, listToMaybe)
import Shared

type E = Int

-- | Universe of discourse.
univ :: [E]
univ = [1 .. 100]

newtype Var = Var Char
  deriving (Eq, Ord, Show)

-- | A referent system: each variable's values, newest first. No empty stacks.
type G = M.Map Var [E]

-- | A domain: how many referents each variable has.
type Counts = M.Map Var Int

data State = State !Counts (G -> Bool)

instance Domain Counts where
  zero = M.empty
  widen = M.unionWith max
  narrow = M.intersectionWith min
  diff = M.differenceWith (\m n -> if m > n then Just (m - n) else Nothing)

-- | Add counts: the referents of both.
plus :: Counts -> Counts -> Counts
plus = M.unionWith (+)

-- Referent systems

-- | Drop a variable's newest value.
pop :: Var -> G -> G
pop = M.update (\xs -> case drop 1 xs of [] -> Nothing; ys -> Just ys)

-- | Drop the newest @n@ values of each variable, per a domain.
popBy :: Counts -> G -> G
popBy c g = M.foldrWithKey (\v n h -> iterate (pop v) h !! n) g c

-- | Every choice of fresh values for a domain, as stacks to push.
witnesses :: Counts -> [G]
witnesses = traverse (\n -> replicateM n univ)

-- | Push fresh values on top of a referent system.
pushAll :: G -> G -> G
pushAll = M.unionWith (++)

-- | The variables' newest values, failing as soon as the result is demanded
-- if any is unvalued.
resolve :: [Var] -> G -> [E]
resolve vs g = fromMaybe (error ("Un-familiar: " ++ show vs)) (traverse (\v -> M.lookup v g >>= listToMaybe) vs)

-- States

instance System State where
  type Dom State = Counts
  dom (State d _) = d
  top d = State d (const True)
  complement (State d f) = State d (not . f)

  -- Add unconstrained referents: the state ignores the newest values.
  extendBy c (State d s) = State (d `plus` c) (s . popBy c)

  -- Existentially close referents: some fresh values satisfy the state.
  reduceBy c (State d s) = State (d `diff` c) (\g -> any (\j -> s (pushAll j g)) (witnesses c))

  infoMeet (State d s) (State _ t) = State d (liftA2 (&&) s t)
  infoJoin (State d s) (State _ t) = State d (liftA2 (||) s t)

-- | Dekker's conjunction: the left state sees the input minus the right
-- state's referents. Nothing can clash, so nothing is checked.
merge :: State -> State -> State
merge (State d s) (State d' t) = State (d `plus` d') (\g -> s (popBy d' g) &&! t g)

-- | Zeevat's symmetric merge.
mergeSymm :: State -> State -> State
mergeSymm (State d s) (State d' t) = State (d `plus` d') (\g -> s g && t g)

-- | Enumerate all satisfying referent systems for a state.
sat :: State -> [G]
sat (State d f) = filter f (witnesses d)

-- Formulas and interpretations

data Form
  = Rel ([E] -> Bool) [Var]
  | Ex Var
  | Not Form
  | And Form Form

-- | Dynamic evaluation. Only familiarity can fail.
evalDyn :: Form -> State -> Either String State
evalDyn (Rel r vs) s
  | all (`M.member` dom s) vs = Right (s @@ State (dom s) (r . resolve vs))
  | otherwise = Left "Un-familiar"
evalDyn (Ex v) s = Right (extendBy (M.singleton v 1) s)
evalDyn (Not p) s = (s \\) <$> evalDyn p s
evalDyn (And p q) s = evalDyn p s >>= evalDyn q

-- | Static content, following the talk's ⟨⟨φ⟩⟩: a count and a predicate.
-- @evalDyn φ s == s `merge` evalStatic' φ@ when defined (tested below).
evalStatic' :: Form -> State
evalStatic' (Rel r vs) = State zero (\g -> r $! resolve vs g) -- familiarity from @resolve@
evalStatic' (Ex v) = top (M.singleton v 1)
evalStatic' (Not p) = let s = evalStatic' p in complement (reduceBy (dom s) s)
evalStatic' (And p q) = evalStatic' p `merge` evalStatic' q

-- | The symmetric variant: total, up to familiarity. Strawson equivalent to
-- @evalDyn@ only on reuse-free formulas: with shadowing, a symmetric merge
-- resolves a pronoun in the left conjunct to a value pushed on the right.
-- Once novelty is free, conjunction must be asymmetric (as in @PLA@, where
-- every push shifts the indices).
evalStatic'' :: Form -> State
evalStatic'' (Rel r vs) = State zero (\g -> all (`M.member` g) vs && r (resolve vs g))
evalStatic'' (Ex v) = top (M.singleton v 1)
evalStatic'' (Not p) = let s = evalStatic'' p in complement (reduceBy (dom s) s)
evalStatic'' (And p q) = evalStatic'' p `mergeSymm` evalStatic'' q

-- Examples/tests.

gt, lt :: [E] -> Bool
gt [x, y] = x > y
gt _ = error "arity"
lt [x, y] = x < y
lt _ = error "arity"

big, small :: [E] -> Bool
big [x] = x > 50
big _ = error "arity"
small [x] = x < 50
small _ = error "arity"

vx, vy, vz :: Var
vx = Var 'x'
vy = Var 'y'
vz = Var 'z'

s0, s1, ex, ez, ew, sh :: Form
s0 = And (Ex vx) (Ex vy)
s1 = Not (And (Ex vz) (Rel gt [vz, vx]))
ex = And s0 s1
-- | A left conjunct with a free variable next to a right conjunct that introduces one.
ez = And (Ex vx) (And (Rel big [vx]) (Ex vy))
-- | Reintroduces @x@ under negation: a novelty violation in EDPL, shadowing here.
ew = And (And s0 (Rel gt [vx, vy])) (Not (And (Ex vx) (Rel lt [vx, vy])))
-- | Reintroduces @x@ in sequence: the later pronoun sees the newer value.
sh = And (And (Ex vx) (Rel big [vx])) (And (Ex vx) (Rel small [vx]))

-- | Dekker's theorem, exact: @evalDyn φ initState == initState `merge` evalStatic' φ@.
agree :: Form -> Bool
agree f = Right (sat (evalStatic' f)) == (sat <$> evalDyn f initState)

-- | From a state over @x@, @evalDyn@ rejects @Fx ∧ Gy@ as un-familiar, and
-- @merge@ with @evalStatic'@ raises on it, though @Fx@ is false throughout and
-- nothing reads @y@.
unfamiliar :: IO Bool
unfamiliar = do
  let s = top (M.singleton vx 1)
      f = And (Rel (const False) [vx]) (Rel (const True) [vy])
  r <- try (evaluate (length (sat (s `merge` evalStatic' f))))
  pure (either (== "Un-familiar") (const False) (evalDyn f s) && either (\(ErrorCall m) -> "Un-familiar" `isPrefixOf` m) (const False) r)

main :: IO ()
main = do
  putStrLn $ "static' vs dynamic on ex, ez, ew, sh: " ++ show (map agree [ex, ez, ew, sh])
  unfamiliar >>= \b -> putStrLn ("familiarity, Fx false: " ++ show b)
  putStrLn $ "ew (un-novel in EDPL): " ++ show (fmap (length . sat) (evalDyn ew initState)) ++ " referent systems, y = " ++ show [g M.! vy | g <- take 1 (sat (evalStatic' ew))]
  putStrLn $ "sh: " ++ show (length (sat (evalStatic' sh))) ++ " referent systems, e.g. " ++ show [M.toList g | g <- take 1 (sat (evalStatic' sh))]
