module PLA where

import Control.Monad (replicateM)

-- Basic data and types

type E = Int

-- | Universe of discourse.
univ :: [E]
univ = [1 .. 100]

-- | Pronouns are de Bruijn indices.
newtype Pro = Var {getPro :: Int}
  deriving (Eq, Ord)

-- | Stacks of entities.
type Stack = [E]

-- States and operations on states

-- | States are pairs of a length/domain and a set of stacks representing an
-- information state over that domain.
data State = State {dom :: Length, info :: Stack -> Bool}

-- | Length of a state. NB: *not* the length of its stacks, but a representation
-- of how many new referents are introduced. Hence, represents a lower bound on
-- the length of the state's stacks.
type Length = Int

-- | Tautologous state of length @n@.
top :: Length -> State
top n = State n (const True)

-- | Maximal/contradictory state of length @n@.
bottom :: Length -> State
bottom n = State n (const False)

-- | Empty/initial state.
initState :: State
initState = top 0

-- | Extend to a larger domain: @k@ new leading positions are unconstrained,
--   so we simply drop them before applying the original function.
extendBy :: Length -> State -> State
extendBy k (State n f)
  | k >= 0 = State (n + k) (f . drop k)
  | otherwise = error "impossible extendBy; this shouldn't happen"
-- == (`merge` top k)

-- | Restrict to a smaller domain: existentially quantify over @k@ positions.
reduceBy :: Length -> State -> State
reduceBy k (State n f)
  | k <= n = State (n - k) (\e -> any (\e' -> f (e' ++ e)) (replicateM k univ))
  | otherwise = error "impossible projectBy; this shouldn't happen"

-- | State merge
merge :: State -> State -> State
merge (State m f) (State n g) = State (m + n) (\e -> f (drop n e) && g e)

-- | State intersection, same domains.
(@@) :: State -> State -> State
State m f @@ State n g
  | m == n = State m (\e -> f e && g e)
  | otherwise = error "mismatched @@ domains; this shouldn't happen"

-- | Complement: negate the characteristic function. Involutive.
complement :: State -> State
complement (State n f) = State n (not . f)

-- | State difference.
(\\) :: State -> State -> State
s \\ t = s @@ complement (reduceBy (dom t - dom s) t)

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
evalStatic (Rel r vs) = State 0 (r . resolve vs)
evalStatic Ex = top 1
evalStatic (Not p) = let s = evalStatic p in complement (reduceBy (dom s) s)
evalStatic (And p q) = merge (evalStatic p) (evalStatic q)

-- | Dynamic evaluation: update an state with a formula.
evalDPL :: Form -> State -> State
evalDPL (Rel r vs) s = s @@ State (dom s) (r . resolve vs)
evalDPL Ex s = extendBy 1 s
evalDPL (Not p) s = s \\ evalDPL p s
evalDPL (And p q) s = evalDPL q (evalDPL p s)

-- | Enumerate all satisfying stacks.
sat :: State -> [Stack]
sat (State n f) = filter f (replicateM n univ)

-- Dekker 1996/2002: evalDPL φ s ≡ s `merge` evalStatic φ

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
