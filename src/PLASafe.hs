module PLASafe where

import Control.Monad  (replicateM)
import Data.Proxy     (Proxy (..))
import Data.Type.Bool (If)
import GHC.TypeLits
  ( KnownNat,
    Nat,
    natVal,
    type (+),
    type (-),
    type (<=),
    type (<=?),
  )

-- ── Basic types ───────────────────────────────────────────────────────────────

type E     = Int
type Stack = [E]

-- ── Typed variables ───────────────────────────────────────────────────────────

data V (n :: Nat) where
  V :: KnownNat n => V n

data VList (req :: Nat) where
  VNil :: VList 0
  (:&) :: V i -> VList req -> VList (Max (i + 1) req)

infixr 5 :&

resolveV :: VList req -> Stack -> [E]
resolveV VNil      _ = []
resolveV (v :& vs) e = vIdx v e : resolveV vs e

vIdx :: V n -> Stack -> E
vIdx v@V e = e !! fromIntegral (natVal v)

-- ── Type-level arithmetic ─────────────────────────────────────────────────────

type Max    m n = If (m <=? n) n m
type Min    m n = If (m <=? n) m n
type SatSub m n = If (n <=? m) (m - n) 0

-- ── Runtime helper ────────────────────────────────────────────────────────────

natInt :: forall n. KnownNat n => Int
natInt = fromIntegral (natVal (Proxy @n))

-- ── Typed formula ─────────────────────────────────────────────────────────────

-- | @Form req ext@
--   * @req@ — minimum input domain size
--   * @ext@ — net referents introduced
--
--   'Not' and 'And' capture 'KnownNat' evidence so that evaluation
--   never needs to thread an explicit domain-size integer.
data Form (req :: Nat) (ext :: Nat) where
  Rel :: ([E] -> Bool) -> VList req -> Form req 0
  Ex  ::                               Form 0   1
  Not :: KnownNat ext
      => Form req ext
      -> Form req 0
  And :: KnownNat eq
      => Form rp ep -> Form rq eq
      -> Form (Max rp (SatSub rq ep)) (ep + eq)

-- ── Universe ──────────────────────────────────────────────────────────────────

univ :: [E]
univ = [1..100]

-- ── State ─────────────────────────────────────────────────────────────────────

-- | @State n@: characteristic function; domain size lives only in the type.
newtype State (n :: Nat) = State { stack :: Stack -> Bool }

initState :: State 0
initState = State (const True)

-- ── The two dual stack adjustments ────────────────────────────────────────────

-- | Extend to a larger domain: @k@ new leading positions are unconstrained,
--   so we simply drop them before applying the original function.
extendBy :: Int -> (Stack -> Bool) -> Stack -> Bool
extendBy 0 f = f
extendBy k f = extendBy (k - 1) (f . tail)

-- | Restrict to a smaller domain: existentially quantify over @k@ positions.
projectBy :: Int -> (Stack -> Bool) -> Stack -> Bool
projectBy 0 f = f
projectBy k f = projectBy (k - 1) \e -> any (\d -> f (d : e)) univ

-- ── Primitive state operations ────────────────────────────────────────────────

addRef :: State n -> State (n + 1)
addRef (State f) = State (extendBy 1 f)

delRef :: State (n + 1) -> State n
delRef (State f) = State (projectBy 1 f)

complement :: State n -> State n
complement (State f) = State (not . f)

merge :: forall m n. KnownNat n => State m -> State n -> State (m + n)
merge (State f) (State g) = State \e -> f (drop (natInt @n) e) && g e

-- ── Lattice ───────────────────────────────────────────────────────────────────
--
--   Meet and join are exact duals:
--
--     direction  │  common domain  │  adjustment  │  connective
--   ─────────────┼─────────────────┼──────────────┼────────────
--     meet  (/\) │  max (widen)    │  extendBy    │  &&
--     join  (\/) │  min (narrow)   │  projectBy   │  ||

(/\) :: forall m n. (KnownNat m, KnownNat n) => State m -> State n -> State (Max m n)
State f /\ State g =
  let k = max (natInt @m) (natInt @n)
  in State \e -> extendBy (k - natInt @m) f e
              && extendBy (k - natInt @n) g e

(\/) :: forall m n. (KnownNat m, KnownNat n) => State m -> State n -> State (Min m n)
State f \/ State g =
  let k = min (natInt @m) (natInt @n)
  in State \e -> projectBy (natInt @m - k) f e
              || projectBy (natInt @n - k) g e

-- ── Saturation ────────────────────────────────────────────────────────────────

sat :: forall n. KnownNat n => State n -> [Stack]
sat (State f) = filter f (replicateM (natInt @n) univ)

satSafe :: KnownNat ext => Form 0 ext -> [Stack]
satSafe = sat . evalStatic

-- ── Evaluation ────────────────────────────────────────────────────────────────

-- | Core loop over bare characteristic functions.
--   No domain-size integer is threaded: the only runtime size needed is the
--   extension of a 'Not'-subformula, supplied by its 'KnownNat ext' witness.
eval :: Form req ext -> (Stack -> Bool) -> (Stack -> Bool)
eval (Rel r vs)                f = \e -> f e && r (resolveV vs e)
eval Ex                        f = f . tail
eval (Not (p :: Form req' ep)) f = let g = eval p f
                                    in \e -> f e && not (projectBy (natInt @ep) g e)
eval (And p q)                 f = eval q (eval p f)

-- | @req <= n@ is the compile-time domain-size check.
--   No 'KnownNat n' needed: 'eval' never inspects the input domain.
evalDPL :: (req <= n) => Form req ext -> State n -> State (n + ext)
evalDPL form (State f) = State (eval form f)

-- | Static content lives in a domain of size @ext@.
evalStatic :: Form req ext -> State ext
evalStatic (Rel r vs)                = State (r . resolveV vs)
evalStatic Ex                        = State (const True)
evalStatic (Not (p :: Form req' ep)) = State (not . projectBy (natInt @ep) (stack (evalStatic p)))
evalStatic (And p q)                 = merge (evalStatic p) (evalStatic q)

-- ── Examples ──────────────────────────────────────────────────────────────────

gt :: [E] -> Bool
gt [x, y] = x > y
gt _       = error "arity"

-- | @exists x. exists y.@ — two fresh referents, no context needed.
s0 :: Form 0 2
s0 = And Ex Ex

-- | @not (exists x. x > z)@, z at index 2.  @req = 3@ is inferred from
--   @V \@2@, then reduced to 2 by @SatSub 3 1@ from the leading @Ex@.
s1 :: Form 2 0
s1 = Not (And Ex (Rel gt (V @0 :& V @2 :& VNil)))

-- | @s0 ; s1@ — safe from the empty context.
ex :: Form 0 2
ex = And s0 s1

-- | @s1 ; s0@ — requires domain >= 2 on arrival.
ey :: Form 2 2
ey = And s1 s0

-- | Dekker theorem: evalDPL phi s = s /\ evalStatic phi
test :: Bool
test = sat (initState /\ evalStatic ex) == sat (evalDPL ex initState)

-- Compile-time rejection (uncomment to verify):
-- bad = evalDPL ey initState   -- No instance for (2 <= 0)
-- bad = satSafe ey

main :: IO ()
main = print test
