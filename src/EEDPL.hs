module EEDPL where

import Control.Monad (replicateM)
import Data.Either (isRight)
import Data.Foldable (foldl')
import qualified Data.Map as M
import qualified Data.Set as S

-- Basic data and types

-- | The domain of entities is @Int@.
type E = Int

-- | Universe of discourse.
univ :: [E]
univ = [1 .. 100]

-- | Named variables.
newtype Var = Var Char
  deriving (Eq, Ord, Enum, Show)

-- | Partial variable assignments.
type G = M.Map Var E

-- | A State is a domain and an info state.
data State = State {dom :: Domain, info :: Info}

-- | Domains are sets of variables.
type Domain = S.Set Var

-- | Info states are properties of assignments.
type Info = G -> Bool

-- Operations on and in states

-- | Add two domains.
domPlus :: Domain -> Domain -> Domain
domPlus = S.union

-- | Subtract two domains.
domDiff :: Domain -> Domain -> Domain
domDiff = (S.\\)

-- | The empty domain.
domZero :: Domain
domZero = S.empty

-- | The informational meet of two domains.
domMeet :: Domain -> Domain -> Domain
domMeet = S.union

-- | The informational join of two domains.
domJoin :: Domain -> Domain -> Domain
domJoin = S.intersection

-- | The informational meet of two info contents.
infoMeet :: Info -> Info -> Info
infoMeet = liftA2 (&&)

-- | The informational join of two info contents.
infoJoin :: Info -> Info -> Info
infoJoin = liftA2 (||)

-- | Tautologous state over a domain.
top :: Domain -> State
top d = State d (const True)

-- | Maximal/contradictory state over a domain.
bottom :: Domain -> State
bottom d = complement (top d)

-- | The initial info state: empty domain, trivial info content.
initState :: State
initState = top domZero

-- | Add a referent to a state
addRef :: State -> Var -> State
addRef (State d s) v =
  State (d `domPlus` S.singleton v) (s . M.delete v)

-- | Delete a referent from a state
delRef :: State -> Var -> State
delRef (State d s) v =
  State (d `domDiff` S.singleton v) (\g -> any (\x -> s (M.insert v x g)) univ)

-- | Extend a state to a larger domain
extendBy :: Domain -> State -> State
extendBy = flip (foldl' addRef)

-- | Restrict a state to a smaller domain
reduceBy :: Domain -> State -> State
reduceBy = flip (foldl' delRef)

-- | State merge, given disjoint domains. Analogous to PLA.
merge :: State -> State -> State
merge (State d s) (State d' t)
  | d `S.disjoint` d' = State (d `domPlus` d') (\e -> s (M.restrictKeys e d) && t e)
  | otherwise = error "Merge: overlapping domains (novelty)"

-- | State intersection, given same domains.
(@@) :: State -> State -> State
State m f @@ State n g
  | m == n = State m (f `infoMeet` g)
  | otherwise = error "mismatched @@ domains; this shouldn't happen"

-- | State complementation (involutive).
complement :: State -> State
complement (State d f) = State d (not . f)

-- | Subtract two states by restricting the second to the domain of the first.
(\\) :: State -> State -> State
s \\ t = s @@ complement (reduceBy (dom t `domDiff` dom s) t)

-- | Enumerate all satisfying assignments for a state.
sat :: State -> [G]
sat (State d f) = filter f assignments
  where
    vs = S.toList d
    seqs = replicateM (length vs) univ
    assignments = map (M.fromList . zip vs) seqs

-- | Lattice operations with the usual axioms.
class Lattice a where
  -- | join
  (\/) :: a -> a -> a
  -- | meet
  (/\) :: a -> a -> a

-- | States form a lattice.
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

-- | First-order formulas with random assignment.
data Form
  = Rel ([E] -> Bool) [Var]
  | Ex Var
  | Not Form
  | And Form Form

-- | Resolve a sequence of variables at an assignment.
resolve :: [Var] -> G -> [E]
resolve vs g = map (g M.!) vs

-- | Standard dynamic evaluation: update a state with a formula. Uses @Either@
-- to facilitate @fvSem@ below.
evalDyn :: Form -> State -> Either String State
evalDyn (Rel r vs) s
  | S.fromList vs `S.isSubsetOf` dom s =
    Right (s @@ State (dom s) (r . resolve vs))
  | otherwise = Left "Un-familiar"
evalDyn (Ex v) s@(State d _)
  | v `S.member` d = Left "Un-novel"
  | otherwise = Right (addRef s v)
evalDyn (Not p) s = (s \\) <$> evalDyn p s
evalDyn (And p q) s = evalDyn p s >>= evalDyn q

-- | Static content of a formula. Indefinites are variables (or vice versa).
evalStatic :: Form -> State
evalStatic (Rel r vs) = State (S.fromList vs) (r . resolve vs)
evalStatic (Ex v) = top (S.singleton v)
evalStatic (Not p) = complement prej
  where
    pSem = evalStatic p
    vars = S.toList (dom pSem)
    prej = bottom (fvSem vars (evalDyn p)) \/ pSem
evalStatic (And p q) = evalStatic p /\ evalStatic q

-- Dekker 1996 proves:
-- When defined: evalDyn phi s == s /\ evalStatic phi (Strawson equivalence)
-- We add: evalDyn phi s == s `merge` evalStatic' phi (equivalence)

-- | Static content of a formula, *with* novelty and familiarity, following
-- @PLA@. It is crucial that @info s@ is a partial @G -> Bool@ function, and so
-- this can't be replicated in @EDPL@. Indefinites and variables kept separate.
evalStatic' :: Form -> State
evalStatic' (Rel r vs) = State domZero (r . resolve vs)     -- familiarity from @resolve@
evalStatic' (Ex v) = top (S.singleton v)
evalStatic' (Not p) = let s = evalStatic' p in complement (reduceBy (dom s) s)
evalStatic' (And p q) = evalStatic' p `merge` evalStatic' q -- novelty from @merge@

-- | Helper function for finding free variables semantically. Needs @Either@.
fvSem :: [Var] -> (State -> Either err State) -> Domain
fvSem vars upd = go vars initState (S.fromList vars)
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

-- | Syntactically finding free variables.
fvSyn :: Form -> Domain
fvSyn (Rel _ vs) = S.fromList vs
fvSyn (Ex _)     = domZero
fvSyn (Not p)    = fvSyn p
fvSyn (And p q)  = fvSyn p `domPlus` (fvSyn q `domDiff` ivSyn p)

-- | Syntactically finding introduced variables.
ivSyn :: Form -> Domain
ivSyn (Rel _ _)  = domZero
ivSyn (Ex v)     = S.singleton v
ivSyn (Not _)    = domZero
ivSyn (And p q)  = ivSyn p `domPlus` ivSyn q

-- Examples/tests.

gt :: [E] -> Bool
gt [x, y] = x > y
gt _      = error "arity"

lt :: [E] -> Bool
lt [x, y] = x < y
lt _     = error "arity"

s0, s1, ex, ey :: Form
-- | There is an @x@ and there is a @y@.
s0 = And (Ex (Var 'x')) (Ex (Var 'y'))
-- | There is no @z@ greater than @x@.
s1 = Not (And (Ex (Var 'z')) (Rel gt [Var 'z', Var 'x']))
-- | Conjoining in anaphoric order.
ex = And s0 s1
-- | Conjoining in cataphoric order.
ey = And s1 s0

test0 :: Bool
test0 = Right (sat (evalStatic  ex)) == (sat <$> evalDyn ex initState)

test1 :: Bool
test1 = Right (sat (evalStatic' ex)) == (sat <$> evalDyn ex initState)

main :: IO ()
main = do
  putStrLn $ "test0 (static  vs DPL): " ++ show test0
  putStrLn $ "test1 (static' vs DPL): " ++ show test1
