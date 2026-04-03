module PLAMin where

import Control.Monad (replicateM)

-- Basic types

type E = Int

type Stack = [E]

newtype Var = Var {getVar :: Int}
  deriving (Eq, Ord)

-- | Information aggregate: domain and an info state over that domain.
data Aggregate d i = State {dom :: d, info :: i}
  deriving Functor

type State = Aggregate Int (Stack -> Bool)

-- | Variable-free first-order formulas with random assignment.
data Form
  = Rel ([E] -> Bool) [Var]
  | Ex
  | Not Form
  | And Form Form

-- | Universe of discourse.
univ :: [E]
univ = [1 .. 100]

-- States and operations

-- | Tautologous state of length @n@.
top :: Int -> State
top n = State n (const True)

-- | Empty/initial state.
initState :: State
initState = top 0

-- | Stack predicate conjunction.
(@@) :: (Stack -> Bool) -> (Stack -> Bool) -> Stack -> Bool
f @@ g = \e -> f e && g e

-- | Extend to a larger domain: @k@ new leading positions are unconstrained,
--   so we simply drop them before applying the original function.
extendBy :: Int -> State -> State
extendBy k (State n f)
  | k >= 0 = State (n + k) (f . drop k)
  | otherwise = error "impossible extendBy; this shouldn't happen"
  -- == (`merge` top k)

-- | Restrict to a smaller domain: existentially quantify over @k@ positions.
projectBy :: Int -> State -> State
projectBy k (State n f)
  | k <= n = State (n - k) (\e -> any (\e' -> f (e' ++ e)) (replicateM k univ))
  | otherwise = error "impossible projectBy; this shouldn't happen"

-- | State merge
merge :: State -> State -> State
merge (State m f) (State n g) = State (m + n) ((f . drop n) @@ g)

-- | State difference.
(\\) :: State -> State -> State
s \\ t = State (dom s) (info s @@ info (complement tX))
  where
    tX = projectBy (dom t - dom s) t

-- | Complement: negate the characteristic function. Involutive.
complement :: State -> State
complement = fmap (not .)

-- Materialization

-- | Enumerate all satisfying stacks.
sat :: State -> [Stack]
sat (State n f) = filter f (replicateM n univ)

-- | Resolve variables against a stack.
resolve :: [Var] -> Stack -> [E]
resolve vs e = map (\(Var i) -> e !! i) vs

-- Evaluation

-- | Static content of a formula.
evalStatic :: Form -> State
evalStatic (Rel r vs) = State 0 (r . resolve vs)
evalStatic Ex = top 1
evalStatic (Not p) = let s = evalStatic p in complement (projectBy (dom s) s)
evalStatic (And p q) = merge (evalStatic p) (evalStatic q)

-- | Dynamic evaluation: update an state with a formula.
evalDPL :: Form -> State -> State
evalDPL (Rel r vs) (State n f) = State n (f @@ (r . resolve vs))
evalDPL Ex s = extendBy 1 s
evalDPL (Not p) s = s \\ evalDPL p s
evalDPL (And p q) s = evalDPL q (evalDPL p s)

-- Dekker 1996: evalDPL φ s ≡ s `merge` evalStatic φ

-- Examples

gt :: [E] -> Bool
gt [x, y] = x > y
gt _      = error "arity"

s0, s1, ex, ey :: Form
s0 = And Ex Ex
s1 = Not (And Ex (Rel gt [Var 0, Var 2]))
ex = And s0 s1
ey = And s1 s0

-- | Test the Dekker theorem: evalDPL φ initState ≡ initState `merge` evalStatic φ
test :: Bool
test = sat (initState `merge` evalStatic ex) == sat (evalDPL ex initState)

main :: IO ()
main = print test
