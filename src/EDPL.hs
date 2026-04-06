module EDPL where

import Data.Either (isRight)
import Data.Foldable (foldl')
import qualified Data.Map as M
import qualified Data.Set as S

-- Basic data and types

type E = Int

-- | Universe of discourse.
univ :: [E]
univ = [1 .. 100]

data Var = W | X | Y | Z
  deriving (Eq, Bounded, Ord, Enum, Show)

vars :: [Var]
vars = [minBound ..]

-- | Partial assignments as maps
type G = M.Map Var E

-- States and operations on states

-- | A State is a domain and a set of partial assignments over that domain
data State = State {dom :: Domain, info :: S.Set G}
  deriving (Show, Eq)

-- | Domains are sets of variables
type Domain = S.Set Var

-- | Add a referent to a state
addRef :: State -> Var -> State
addRef (State d s) v =
  State
    (S.insert v d)
    (S.fromList [M.insert v x g | g <- S.toList s, x <- univ])

-- | Delete a referent from a state
delRef :: State -> Var -> State
delRef (State d s) v =
  State
    (S.delete v d)
    (S.map (M.delete v) s)

-- | Tautologous state over a domain
top :: Domain -> State
top = foldl' addRef initState

-- | Maximal/contradictory state over a domain
bottom :: Domain -> State
bottom d = State d S.empty

-- | The initial info state: empty domain, singleton state with an empty assignment
initState :: State
initState = State S.empty (S.singleton M.empty)

-- | Extend a state to a larger domain
extendBy :: Domain -> State -> State
extendBy d s = foldl' addRef s d

-- | Restrict a state to a smaller domain
reduceBy :: Domain -> State -> State
reduceBy d t = foldl' delRef t d

-- | State intersection, same domains.
(@@) :: State -> State -> State
State m s @@ State n t
  | m == n = State m (s `S.intersection` t)
  | otherwise = error "mismatched @@ domains; this shouldn't happen"

-- | Subtract two states by restricting the second to the domain of the first
(\\) :: State -> State -> State
s \\ t = s @@ complement (reduceBy (dom t S.\\ dom s) t)

-- | State complementation; involutive
complement :: State -> State
complement (State d s) = State d (info (top d) S.\\ s)

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
     in State d (sE `S.intersection` tE)

  s \/ t =
    let d = dom s `S.intersection` dom t
        sR = info (reduceBy (dom s S.\\ d) s)
        tR = info (reduceBy (dom t S.\\ d) t)
     in State d (sR `S.union` tR)

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
      s = info (top d)
   in State d (S.filter (r . resolve vs) s)
evalStatic (Ex v) = top (S.singleton v)
evalStatic (Not p) = complement prej
  where
    pSem = evalStatic p
    varL = S.toList (dom pSem)
    prej = bottom (fvSem varL (evalDPL p)) \/ pSem
evalStatic (And p q) = evalStatic p /\ evalStatic q

-- | Dynamic evaluation: update an state with a formula.
evalDPL :: Form -> State -> Either String State
evalDPL (Rel r vs) (State d s)
  | S.fromList vs `S.isSubsetOf` d =
      Right (State d (S.filter (r . resolve vs) s))
  | otherwise = Left "Un-familiar"
evalDPL (Ex v) s@(State d _)
  | v `S.member` d = Left "Un-novel"
  | otherwise = Right (addRef s v)
evalDPL (Not p) s = (s \\) <$> evalDPL p s
evalDPL (And p q) s = evalDPL p s >>= evalDPL q

-- Dekker 1996 proves:
-- when defined, evalDPL phi s == s /\ evalStatic phi

{-
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
-}

fvSem :: [Var] -> (State -> Either err State) -> Domain
fvSem candidates upd = go candidates initState (S.fromList vars)
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
s0 = And (Ex X) (Ex Y)
s1 = Not (And (Ex Z) (Rel gt [Z, X]))
ex = And s0 s1
ey = And s1 s0

test :: Bool
test = Right (evalStatic ex) == evalDPL ex initState

main :: IO ()
main = print test
