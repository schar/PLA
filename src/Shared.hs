{-# LANGUAGE FlexibleContexts, TypeFamilies #-}

-- | What the fragments share. A state is tagged with a domain of referents
-- and carries an info content; each fragment supplies the primitives, and the
-- operations below follow.
module Shared where

-- | Domains of referents.
class Domain d where
  zero :: d

  -- | Widen to both.
  widen :: d -> d -> d

  -- | Narrow to the common part.
  narrow :: d -> d -> d

  -- | Remove the second from the first.
  diff :: d -> d -> d

-- | De Bruijn domains: how many referents.
instance Domain Int where
  zero = 0
  widen = max
  narrow = min
  diff = (-)

-- | States over a domain.
class System s where
  type Dom s
  dom :: s -> Dom s

  -- | No information about a domain.
  top :: Dom s -> s

  complement :: s -> s

  -- | Add unconstrained referents.
  extendBy :: Dom s -> s -> s

  -- | Existentially close referents.
  reduceBy :: Dom s -> s -> s

  -- | Intersect and union the info of two states over the same domain.
  infoMeet, infoJoin :: s -> s -> s

bottom :: System s => Dom s -> s
bottom = complement . top

initState :: (System s, Domain (Dom s)) => s
initState = top zero

-- | Intersection, given the same domain.
(@@) :: (System s, Eq (Dom s)) => s -> s -> s
s @@ t
  | dom s == dom t = s `infoMeet` t
  | otherwise = error "mismatched @@ domains; this shouldn't happen"

-- | Subtract, restricting the second state to the domain of the first.
(\\) :: (System s, Domain (Dom s), Eq (Dom s)) => s -> s -> s
s \\ t = s @@ complement (reduceBy (dom t `diff` dom s) t)

-- The lattice. For named variables (EDPL, EEDPL) these are Dekker's product
-- and common ground, and the identification of referents across states is
-- canonical. For positional systems (PLA's stacks, SEDPL's per-variable
-- stacks) it is not: @extendBy@ and @reduceBy@ treat the smaller state's
-- referents as the older ones, the convention @merge@ presupposes, and the
-- laws hold relative to that alignment. Those systems don't use these.

-- | Lattice meet: widen both to the larger domain, intersect.
(/\) :: (System s, Domain (Dom s)) => s -> s -> s
s /\ t =
  let d = dom s `widen` dom t
   in extendBy (d `diff` dom s) s `infoMeet` extendBy (d `diff` dom t) t

-- | Lattice join: narrow both to the smaller domain, union.
(\/) :: (System s, Domain (Dom s)) => s -> s -> s
s \/ t =
  let d = dom s `narrow` dom t
   in reduceBy (dom s `diff` d) s `infoJoin` reduceBy (dom t `diff` d) t
