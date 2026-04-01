module PLA where

import Control.Monad (replicateM)

-- Basic types

type E = Int

type Stack = [E]

newtype Var = Var
  {getVar :: Int}
  deriving (Eq, Ord)

-- | Information state: domain size and characteristic function.
data State a = State
  { dom :: Int,
    stack :: a -> Bool
  }

data Form
  = Rel ([E] -> Bool) [Var]
  | Ex
  | Not Form
  | And Form Form

-- Universe

univ :: [E]
univ = [1 .. 100]

-- States and operations

-- | Add a referent (prepend an unconstrained position).
addRef :: State Stack -> State Stack
addRef (State n f) = State (n + 1) (f . tail)

-- | Delete the newest referent (existentially project the first position).
delRef :: State Stack -> State Stack
delRef (State n f) = State (n - 1) \e -> any (\d -> f (d : e)) univ


top :: Int -> State a
top n = State n (const True)

-- | Contradictory state.
bottom :: Int -> State a
bottom n = State n (const False)

-- | Empty context.
initState :: State a
initState = State 0 (const True)

-- | Extend to a larger domain.
extend :: State Stack -> Int -> State Stack
extend s k
  | dom s <= k = iterate addRef s !! (k - dom s)
  | otherwise  = error "extend: target smaller than source"

-- | Restrict to a smaller domain.
restrict :: State Stack -> Int -> State Stack
restrict s k
  | k <= dom s = iterate delRef s !! (dom s - k)
  | otherwise   = error "restrict: target larger than source"

-- | State difference.
(\\) :: State Stack -> State Stack -> State Stack
State n f \\ t =
  let g = stack (restrict t n)
   in State n \e -> f e && not (g e)

-- | Complement: negate the characteristic function. Involutive.
complement :: State a -> State a
complement (State n f) = State n (not . f)

-- Lattice (right-aligned identity linking)

class Lattice a where
  (\/) :: a -> a -> a -- join
  (/\) :: a -> a -> a -- meet

instance Lattice (State Stack) where
  -- Meet: extend both to max domain, intersect
  s /\ t =
    let k = max (dom s) (dom t)
        f = stack (extend s k)
        g = stack (extend t k)
    in State k \e -> f e && g e

  -- Join: restrict both to min domain, union
  s \/ t =
    let k = min (dom s) (dom t)
        f = stack (restrict s k)
        g = stack (restrict t k)
    in State k \e -> f e || g e

-- Materialization

-- | Enumerate all satisfying stacks.
sat :: State Stack -> [Stack]
sat (State n f) = filter f (replicateM n univ)

-- | Resolve variables against a stack.
resolve :: Stack -> [Var] -> [E]
resolve e = map \(Var i) -> e !! i

-- Evaluation

-- | Dekker's dynamic merge (Observation 15).
merge :: State Stack -> State Stack -> State Stack
merge (State m f) (State n g) = State (m + n) \e -> f (drop n e) && g e

-- | Static content of a formula.
evalStatic :: Form -> State Stack
evalStatic (Rel r vs) = State 0 \e -> r (resolve e vs)
evalStatic Ex = top 1
evalStatic (Not p) = complement (restrict (evalStatic p) 0)
evalStatic (And p q) = merge (evalStatic p) (evalStatic q)

-- | Dynamic evaluation: update an state with a formula.
evalDPL :: Form -> State Stack -> State Stack
evalDPL (Rel r vs) (State n f) = State n \e -> f e && r (resolve e vs)
evalDPL Ex s = addRef s
evalDPL (Not p) s = s \\ evalDPL p s
evalDPL (And p q) s = evalDPL q (evalDPL p s)

-- Dekker 1996: evalDPL φ s ≡ s /\ evalStatic φ

-- Examples

gt :: [E] -> Bool
gt [x, y] = x > y
gt _      = error "arity"

s0, s1, ex, ey :: Form
s0 = And Ex Ex
s1 = Not (And Ex (Rel gt [Var 0, Var 2]))
ex = And s0 s1
ey = And s1 s0

-- | Test the Dekker theorem: evalDPL φ initState ≡ initState /\ evalStatic φ
test :: Bool
test = sat (initState /\ evalStatic ex) == sat (evalDPL ex initState)

main :: IO ()
main = print test
