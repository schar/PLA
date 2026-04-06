module PLA where

import Control.Monad (replicateM)

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

-- | States are pairs of a length/domain and a set of stacks representing an
-- information state over that domain.
data State = State {dom :: Length, info :: Stack -> Bool}

-- | Length of a state. NB: *not* the length of its stacks, but a contract
-- representing how many new referents are introduced. (Hence, represents a
-- lower bound on the length of the state's stacks.)
type Length = Int

domPlus :: Length -> Length -> Length
domPlus = (+)

domDiff :: Length -> Length -> Length
domDiff = (-)

domZero :: Length
domZero = 0

domMeet :: Length -> Length -> Length
domMeet = max

domJoin :: Length -> Length -> Length
domJoin = min

infoMeet :: (Stack -> Bool) -> (Stack -> Bool) -> Stack -> Bool
infoMeet f g e = f e && g e

infoJoin:: (Stack -> Bool) -> (Stack -> Bool) -> Stack -> Bool
infoJoin f g e = f e || g e

-- | Tautologous state of length @n@.
top :: Length -> State
top n = State n (const True)

-- | Contradictory state of length @n@.
bottom :: Length -> State
bottom n = complement (top n)

-- | Empty/initial state.
initState :: State
initState = top domZero

-- | Extend to a larger domain: @k@ new leading positions are unconstrained,
--   so we simply drop them before applying the original function.
extendBy :: Length -> State -> State
extendBy k (State n f)
  | k >= domZero = State (n `domPlus` k) (f . drop k)
  | otherwise = error "impossible extendBy; this shouldn't happen"
-- == (`merge` top k)

-- | Restrict to a smaller domain: existentially quantify over @k@ positions.
reduceBy :: Length -> State -> State
reduceBy k (State n f)
  | k <= n = State (n - k) (\e -> any (\e' -> f (e' ++ e)) (replicateM k univ))
  | otherwise = error "impossible projectBy; this shouldn't happen"

-- | State merge
merge :: State -> State -> State
merge (State m f) (State n g) = State (m `domPlus` n) (\e -> f (drop n e) && g e)
  -- == State (m `domPlus` n) (f . drop n) @@ State (m `domPlus` n) g

-- | State intersection, same domains.
(@@) :: State -> State -> State
State m f @@ State n g
  | m == n = State m (f `infoMeet` g)
  | otherwise = error "mismatched @@ domains; this shouldn't happen"

-- | Complement: negate the characteristic function. Involutive.
complement :: State -> State
complement (State n f) = State n (not . f)

-- | State difference. @reduceBy@ will throw error if @dom s > dom t@.
(\\) :: State -> State -> State
s \\ t = s @@ complement (reduceBy (dom t `domDiff` dom s) t)

-- | Lattice operations with the usual axioms
class Lattice a where
  -- | join
  (\/) :: a -> a -> a
  -- | meet
  (/\) :: a -> a -> a

-- | States form a lattice
instance Lattice State where
  s /\ t =
    let d = dom s `domMeet` dom t
        sE = info (extendBy (d `domDiff` dom s) s)
        tE = info (extendBy (d `domDiff` dom t) t)
     in State d (sE `infoMeet` tE)

  s \/ t =
    let d = dom s `domJoin` dom t
        sR = info (reduceBy (dom s `domDiff` d) s)
        tR = info (reduceBy (dom t `domDiff` d) t)
     in State d (sR `infoJoin` tR)

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
evalStatic (Rel r vs) = State domZero (r . resolve vs)
evalStatic Ex = top 1
evalStatic (Not p) = let s = evalStatic p in complement (reduceBy (dom s) s)
evalStatic (And p q) = merge (evalStatic p) (evalStatic q)

-- | Dynamic evaluation: update an state with a formula.  Dekker 1996/2002:
-- @evalDPL φ s ≡ s `merge` evalStatic φ@.
evalDPL :: Form -> State -> State
evalDPL (Rel r vs) s = s @@ State (dom s) (r . resolve vs)
evalDPL Ex s = extendBy 1 s
evalDPL (Not p) s = s \\ evalDPL p s
evalDPL (And p q) s = evalDPL q (evalDPL p s)

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
test = sat (initState `merge` evalStatic ex) == sat (evalDPL ex initState)

main :: IO ()
main = print test
