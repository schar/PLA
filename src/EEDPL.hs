module EEDPL where

import Control.Monad (replicateM)
import Data.Either (isRight)
import Data.Foldable (foldl')
import qualified Data.Map as M
import qualified Data.Set as S

-- Basic data and types

type E = Int

-- | Universe of discourse.
univ :: [E]
univ = [1 .. 100]

newtype Var = Var Char
  deriving (Eq, Ord, Enum, Show)

-- | Partial assignments as maps
type G = M.Map Var E

-- States and operations on states

-- | A State is a domain and a set of partial assignments over that domain
data State = State {dom :: Domain, info :: G -> Bool}

-- | Domains are sets of variables
type Domain = S.Set Var

-- | Add a referent to a state
addRef :: State -> Var -> State
addRef (State d s) v =
  State (S.insert v d) (s . M.delete v)

-- | Delete a referent from a state
delRef :: State -> Var -> State
delRef (State d s) v =
  State (S.delete v d) (\g -> any (\x -> s (M.insert v x g)) univ)

-- | Tautologous state over a domain
top :: Domain -> State
top d = State d (const True)

-- | Maximal/contradictory state over a domain
bottom :: Domain -> State
bottom d = State d (const False)

-- | The initial info state: empty domain, singleton state with an empty assignment
initState :: State
initState = top S.empty

-- | Extend a state to a larger domain
extendBy :: Domain -> State -> State
extendBy d s = foldl' addRef s d

-- | Restrict a state to a smaller domain
reduceBy :: Domain -> State -> State
reduceBy d t = foldl' delRef t d

-- | State intersection, same domains.
(@@) :: State -> State -> State
State m f @@ State n g
  | m == n = State m (\e -> f e && g e)
  | otherwise = error "mismatched @@ domains; this shouldn't happen"

-- | Subtract two states by restricting the second to the domain of the first
(\\) :: State -> State -> State
s \\ t = s @@ complement (reduceBy (dom t S.\\ dom s) t)

-- | State complementation; involutive
complement :: State -> State
complement (State d f) = State d (not . f)

-- | Lattice operations with the usual axioms
class Lattice a where
  -- | join
  (\/) :: a -> a -> a
  -- | meet
  (/\) :: a -> a -> a

-- | States form a natural lattice
instance Lattice State where
  s /\ t =
    let d = dom s `S.union` dom t
        sE = info (extendBy (d S.\\ dom s) s)
        tE = info (extendBy (d S.\\ dom t) t)
     in State d (\g -> sE g && tE g)

  s \/ t =
    let d = dom s `S.intersection` dom t
        sR = info (reduceBy (dom s S.\\ d) s)
        tR = info (reduceBy (dom t S.\\ d) t)
     in State d (\g -> sR g || tR g)

-- Formulas and dynamic and static interpretations

-- | Variable-free first-order formulas with random assignment.
data Form
  = Rel ([E] -> Bool) [Var]
  | Ex Var
  | Not Form
  | And Form Form

-- | Resolve a sequence of variables at an assignment.
resolve :: [Var] -> G -> [E]
resolve vs g = map (g M.!) vs

-- | Static content of a formula.
evalStatic :: Form -> State
evalStatic (Rel r vs) =
  let d = S.fromList vs
   in State d (r . resolve vs)
evalStatic (Ex v) = top (S.singleton v)
evalStatic (Not p) = complement prej
  where
    pSem = evalStatic p
    vars = S.toList (dom pSem)
    prej = bottom (fvSem vars (evalDPL p)) \/ pSem
evalStatic (And p q) = evalStatic p /\ evalStatic q

-- | Dynamic evaluation: update an state with a formula.
evalDPL :: Form -> State -> Either String State
evalDPL (Rel r vs) s
  | S.fromList vs `S.isSubsetOf` dom s =
    Right (s @@ State (dom s) (r . resolve vs))
  | otherwise = Left "Un-familiar"
evalDPL (Ex v) s@(State d _)
  | v `S.member` d = Left "Un-novel"
  | otherwise = Right (addRef s v)
evalDPL (Not p) s = (s \\) <$> evalDPL p s
evalDPL (And p q) s = evalDPL p s >>= evalDPL q

-- | Enumerate all satisfying assignments.
sat :: State -> [G]
sat (State d f) = filter f assignments
  where
    vs = S.toList d
    seqs = replicateM (length vs) univ
    assignments = map (M.fromList . zip vs) seqs

-- Dekker 1996 proves:
-- when defined, evalDPL phi s == s /\ evalStatic phi

fvSyn :: Form -> Domain
fvSyn (Rel _ vs) = S.fromList vs
fvSyn (Ex _)     = S.empty
fvSyn (Not p)    = fvSyn p
fvSyn (And p q)  = fvSyn p `S.union` (fvSyn q `S.difference` ivSyn p)

ivSyn :: Form -> Domain
ivSyn (Rel _ _)  = S.empty
ivSyn (Ex v)     = S.singleton v
ivSyn (Not _)    = S.empty
ivSyn (And p q)  = ivSyn p `S.union` ivSyn q

fvSem :: [Var] -> (State -> Either err State) -> Domain
fvSem candidates upd = go candidates initState (S.fromList candidates)
  where
    go _ _ acc
      | S.null acc = acc
    go [] s acc
      | isRight (upd s) = acc `S.intersection` dom s
      | otherwise = acc
    go (v : vs) s acc =
      let acc1 = go vs s acc
          acc2 = go vs (addRef s v) acc1
       in acc2

-- Examples
gt :: [E] -> Bool
gt [x, y] = x > y
gt _      = error "arity"

s0, s1, ex, ey :: Form
s0 = And (Ex (Var 'x')) (Ex (Var 'y'))
s1 = Not (And (Ex (Var 'z')) (Rel gt [Var 'z', Var 'x']))
ex = And s0 s1
ey = And s1 s0

test :: Bool
test = (sat <$> Right (evalStatic ex)) == (sat <$> evalDPL ex initState)

main :: IO ()
main = print test
