# PLA

Predicate Logic with Anaphora -- Haskell implementations of static and dynamic
first-order interpretations following Dekker
([1996](https://doi.org/10.1007/BF00628200),
[2002](https://doi.org/10.1023/A:1017575313451)).

Five perspectives:

- **EDPL** — Assignments as maps. States as sets of assignments tagged with a
common domain. Ill-formed updates (an unfamiliar variable, a non-novel
indefinite) return `Left`. Natural lattice structure on states.
- **EEDPL** — A more efficient version that accumulates constraints on
assignments inside states (info states are predicates) and delays
materializing them as long as possible. Otherwise equivalent to EDPL.
- **PLA** — Stack-based (de Bruijn) assignments. States are predicates of stacks
tagged with their common length. Ill-formed updates are not checked; an
out-of-range pronoun errors when a state is materialized.
- **PLASafe** — Stack-based assignments with type-level domain and extension
indices, ensuring well-formedness at compile time.
- **SEDPL** — EDPL over referent systems (Vermeulen's sequence semantics): a
variable points to a stack of values, so reintroducing it shadows the old
value rather than clashing. No novelty condition; identical to EDPL wherever
EDPL is defined, and `evalDyn` is exactly `merge` with `evalStatic'` everywhere.

Each system provides a dynamic interpretation `evalDyn` and a static one
`evalStatic`. In the PLA fragments they are equivalent given `merge`. In the
EDPL fragments they are Strawson-equivalent given `/\` (`evalStatic` is total,
but `evalDyn` is not). EEDPL adds two further static interpretations:

- `evalStatic'`, with novelty from `merge` and from the disjoint union of
  assignments under negation, and familiarity from a partial info function, which
  is exactly equivalent to `evalDyn` given `merge`;
- `evalStatic''`, with only introduced variables in a state's domain and
  Zeevat's symmetric merge for conjunction: total, with no novelty or
  familiarity conditions, and Strawson-equivalent to `evalDyn`.

## Build & run

Requires GHC 9.10 or later ([ghcup](https://www.haskell.org/ghcup/)).

```bash
cabal build all
cabal run EDPL # or: EEDPL / SEDPL / PLA / PLASafe
```

```bash
cabal repl EDPL # or: EEDPL / SEDPL / PLA / PLASafe
```

The QuickCheck suite for EEDPL (Strawson and merge equivalence, lattice laws,
syntactic vs. semantic free variables):

```bash
cabal test
```
