{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, TypeFamilies #-}

module EDPL (module EDPL, module Shared) where

import Data.Either (isRight)
import Data.List (subsequences)
import qualified Data.Map as M
import qualified Data.Set as S
import Shared

-- Basic data and types

type E = Int

-- | Universe of discourse.
univ :: [E]
univ = [1 .. 100]

-- | Named variables.
newtype Var = Var Char
  deriving (Eq, Ord, Enum, Show)

-- | Partial variable assignments.
type G = M.Map Var E

-- States and operations on states

-- | A State is a domain and a set of assignments over that domain.
data State = State Vars (S.Set G)
  deriving (Eq, Show)

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
  top = foldl' addRef (State S.empty (S.singleton M.empty))
  complement (State d s) = let State _ t = top d in State d (t S.\\ s)
  extendBy d s = foldl' addRef s d
  reduceBy d t = foldl' delRef t d
  infoMeet (State d s) (State _ t) = State d (S.intersection s t)
  infoJoin (State d s) (State _ t) = State d (S.union s t)

-- | Add a referent to a state
addRef :: State -> Var -> State
addRef (State d s) v = State (S.insert v d) (S.fromList [M.insert v x g | g <- S.toList s, x <- univ])

-- | Delete a referent from a state
delRef :: State -> Var -> State
delRef (State d s) v = State (S.delete v d) (S.map (M.delete v) s)

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

-- | Static content of a formula.
evalStatic :: Form -> State
evalStatic (Rel r vs) =
  let d = S.fromList vs
      State _ s = top d
   in State d (S.filter (r . resolve vs) s)
evalStatic (Ex v) = top (S.singleton v)
evalStatic (Not p) = complement prej
  where
    pSem = evalStatic p
    vars = S.toList (dom pSem)
    prej = bottom (fvSem vars (evalDyn p)) \/ pSem
evalStatic (And p q) = evalStatic p /\ evalStatic q

-- No @evalStatic''@ here (see @EEDPL@). A @dom@ holding only *introduced*
-- variables needs info that also mentions free variables, i.e. a predicate on
-- assignments. Sets of maps keyed exactly by @dom@ can't express that.

-- | Dynamic evaluation: update an state with a formula.
evalDyn :: Form -> State -> Either String State
evalDyn (Rel r vs) (State d s)
  | S.fromList vs `S.isSubsetOf` d =
      Right (State d (S.filter (r . resolve vs) s))
  | otherwise = Left "Un-familiar"
evalDyn (Ex v) s@(State d _)
  | v `S.member` d = Left "Un-novel"
  | otherwise = Right (addRef s v)
evalDyn (Not p) s = (s \\) <$> evalDyn p s
evalDyn (And p q) s = evalDyn p s >>= evalDyn q

-- Dekker 1996 proves:
-- when defined, evalDyn phi s == s /\ evalStatic phi

fvSyn :: Form -> Vars
fvSyn (Rel _ vs) = S.fromList vs
fvSyn (Ex _)     = S.empty
fvSyn (Not p)    = fvSyn p
fvSyn (And p q)  = fvSyn p `S.union` (fvSyn q `S.difference` ivSyn p)

ivSyn :: Form -> Vars
ivSyn (Rel _ _)  = S.empty
ivSyn (Ex v)     = S.singleton v
ivSyn (Not _)    = S.empty
ivSyn (And p q)  = ivSyn p `S.union` ivSyn q

-- | Free variables, found semantically: the variables common to every domain
-- on which the update is defined. Definedness depends only on the domain, so
-- the probe states carry no assignments.
fvSem :: [Var] -> (State -> Either err State) -> Vars
fvSem vars upd =
  foldr S.intersection (S.fromList vars)
    [d | d <- map S.fromList (subsequences vars), isRight (upd (State d S.empty))]

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
test = Right (evalStatic ex) == evalDyn ex initState

main :: IO ()
main = print test
