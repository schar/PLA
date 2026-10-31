{-# LANGUAGE TypeFamilies #-}

module PLA (module PLA, module Shared) where

import Control.Monad (replicateM)
import Shared

-- Basic data and types

type E = Int

-- | Universe of discourse.
univ :: [E]
univ = [1 .. 100]

-- | Pronouns are de Bruijn indices.
newtype Pro = Var {getPro :: Int}

-- | Stacks of entities.
type Stack = [E]

-- States and operations on states

-- | A state is a length and a property of stacks.
data State = State Length (Stack -> Bool)

-- | Length of a state. NB: *not* the length of its stacks, but a contract
-- representing how many new referents are introduced. (Hence, represents a
-- lower bound on the length of the state's stacks.)
type Length = Int

instance System State where
  type Dom State = Length
  dom (State n _) = n
  top n = State n (const True)
  complement (State n f) = State n (not . f)

  -- @k@ new leading positions are unconstrained, so drop them.
  -- == (`merge` top k)
  extendBy k (State n f)
    | k >= 0 = State (n + k) (f . drop k)
    | otherwise = error "impossible extendBy; this shouldn't happen"

  -- Existentially quantify over @k@ leading positions.
  reduceBy k (State n f)
    | k <= n = State (n - k) (\e -> any (\e' -> f (e' ++ e)) (replicateM k univ))
    | otherwise = error "impossible reduceBy; this shouldn't happen"

  infoMeet (State n f) (State _ g) = State n (liftA2 (&&) f g)
  infoJoin (State n f) (State _ g) = State n (liftA2 (||) f g)

-- | State merge
merge :: State -> State -> State
merge (State m f) (State n g) = State (m + n) (\e -> f (drop n e) && g e)
  -- == State (m + n) (f . drop n) @@ State (m + n) g

-- Formulas and dynamic and static interpretations

-- | Variable-free first-order formulas with random assignment.
data Form
  = Rel ([E] -> Bool) [Pro]
  | Ex
  | Not Form
  | And Form Form

-- | Resolve a sequence of variables at a stack.
resolve :: [Pro] -> Stack -> [E]
resolve vs e = map (\(Var i) -> e !! i) vs

-- | Static content of a formula.
evalStatic :: Form -> State
evalStatic (Rel r vs) = State zero (r . resolve vs)
evalStatic Ex = top 1
evalStatic (Not p) = let s = evalStatic p in complement (reduceBy (dom s) s)
evalStatic (And p q) = merge (evalStatic p) (evalStatic q)

-- | Dynamic evaluation: update an state with a formula.  Dekker 1996/2002:
-- @evalDyn φ s ≡ s `merge` evalStatic φ@.
evalDyn :: Form -> State -> State
evalDyn (Rel r vs) s = s @@ State (dom s) (r . resolve vs)
evalDyn Ex s = extendBy 1 s
evalDyn (Not p) s = s \\ evalDyn p s
evalDyn (And p q) s = evalDyn q (evalDyn p s)

-- | Enumerate all satisfying stacks.
sat :: State -> [Stack]
sat (State n f) = filter f (replicateM n univ)

-- Examples

gt :: [E] -> Bool
gt [x, y] = x > y
gt _      = error "arity"

s0, s1, ex, ey :: Form
s0 = And Ex Ex
s1 = Not (And Ex (Rel gt [Var 0, Var 2]))
ex = And s0 s1
ey = And s1 s0

-- | Test the Dekker theorem on @ex@ at @initState@.
test :: Bool
test = sat (initState `merge` evalStatic ex) == sat (evalDyn ex initState)

main :: IO ()
main = print test
