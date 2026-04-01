module EDPL where

import Data.Either (isRight)
import Data.Foldable (foldl')
import qualified Data.Map as M
import qualified Data.Set as S

-- Basic data and types

data Var = W | X | Y | Z
  deriving (Eq, Bounded, Ord, Enum, Show)

vars :: [Var]
vars = [minBound ..]

type E = Int

univ :: [E]
univ = [1 .. 100]

-- | Partial assignments as maps
type G = M.Map Var E

-- | Domains are sets of variables
type Domain = S.Set Var

-- | A State is a domain and a set of partial assignments over that domain
type State = (Domain, S.Set G)

-- States and operations on states

-- | Add a referent to a state
addRef :: State -> Var -> State
addRef (dom, s) v =
  ( S.insert v dom,
    S.fromList
      [ M.insert v x g
        | g <- S.toList s,
          x <- univ
      ]
  )

-- | Delete a referent from a state
delRef :: State -> Var -> State
delRef (dom, s) v =
  ( S.delete v dom,
    S.map (M.delete v) s
  )

-- | Generate a minimal state given a domain
stateFromDomain :: Domain -> State
stateFromDomain = foldl' addRef initState

-- | Restrict a state to a smaller domain
restrict :: State -> Domain -> State
restrict (domT, t) target
  | target `S.isSubsetOf` domT =
      let diff = domT S.\\ target
       in foldl' delRef (domT, t) diff
  -- (target, S.map (`M.restrictKeys` target) t)
  | otherwise = error "restrict: this shouldn't happen"

-- | Extend a state to a larger domain
extend :: State -> Domain -> State
extend (domS, s) target
  | domS `S.isSubsetOf` target =
      let diff = target S.\\ domS
       in foldl' addRef (domS, s) diff
  | otherwise = error "extend: this shouldn't happen"

-- | Subtract two states by restricting the second to the domain of the first
(\\) :: State -> State -> State
(domS, s) \\ t = (domS, s S.\\ snd (restrict t domS))

-- | State complementation; involutive
complement :: State -> State
complement s@(domS, _) = stateFromDomain domS \\ s

-- | Alias for a minimal state over a domain
top :: Domain -> State
top = stateFromDomain

-- | Maximal/contradictory state over a domain
bottom :: Domain -> State
bottom dom = (dom, S.empty)

-- | The initial info state: empty domain, singleton state with an empty assignment
initState :: State
initState = (S.empty, S.singleton M.empty)

-- | Lattice operations with the usual axioms
class Lattice a where
  -- | join
  (\/) :: a -> a -> a
  -- | meet
  (/\) :: a -> a -> a

-- | States form a natural lattice
instance Lattice State where
  s /\ t =
    let dom = fst s `S.union` fst t
        sE = snd (extend s dom)
        tE = snd (extend t dom)
     in (dom, sE `S.intersection` tE)

  s \/ t =
    let dom = fst s `S.intersection` fst t
        sR = snd (restrict s dom)
        tR = snd (restrict t dom)
     in (dom, sR `S.union` tR)

-- Formulas and dynamic and static interpretations

data Form
  = Rel ([E] -> Bool) [Var]
  | Ex Var
  | Not Form
  | And Form Form

evalDPL :: Form -> State -> Either String State
evalDPL (Rel r vs) (dom, s)
  | S.fromList vs `S.isSubsetOf` dom =
      let proj g = map (g M.!) vs
       in Right (dom, S.filter (r . proj) s)
  | otherwise = Left "Un-familiar"
evalDPL (Ex v) s@(dom, _)
  | v `S.member` dom = Left "Un-novel"
  | otherwise = Right (addRef s v)
evalDPL (Not p) s = (s \\) <$> evalDPL p s
evalDPL (And p q) s = evalDPL p s >>= evalDPL q

evalStatic :: Form -> State
evalStatic (Rel r vs) =
  let dom = S.fromList vs
      s = snd (stateFromDomain dom)
      proj g = map (g M.!) vs
   in (dom, S.filter (r . proj) s)
evalStatic (Ex v) = top (S.singleton v)
evalStatic (Not p) = complement prej
  where
    prej = bottom (fvSem (evalDPL p)) \/ evalStatic p
evalStatic (And p q) = evalStatic p /\ evalStatic q

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

fvSem :: (State -> Either err State) -> Domain
fvSem upd = go vars initState (S.fromList vars)
  where
    go _ _ acc
      | S.null acc = acc
    go [] s acc
      | isRight (upd s) = acc `S.intersection` fst s
      | otherwise = acc
    go (v : vs) s acc =
      let acc1 = go vs s acc
          acc2 = go vs (addRef s v) acc1
       in acc2

-- Examples
s0 :: Form
s0 = And (Ex X) (Ex Y)

s1 :: Form
s1 = Not (And (Ex Z) (Rel gt [Z, X]))
  where
    gt [x, y] = x > y
    gt _ = error "arity"

ex :: Form
ex = And s0 s1

test :: Bool
test = Right (evalStatic ex) == evalDPL ex initState

main :: IO ()
main = print test
