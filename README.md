# PLA

Predicate Logic with Anaphora -- Haskell implementations of static and dynamic
first-order interpretations following Dekker
([1996](https://doi.org/10.1007/BF00628200),
[2002](https://doi.org/10.1023/A:1017575313451)).

Five perspectives:

- **EDPL** — Assignments as maps. States as sets of assignments tagged with a
common domain. Unfamiliar pronouns and non-novel indefinites return `Left`.
Natural lattice structure on states.
- **EEDPL** — The same, with states as predicates on assignments, materialized
only when needed.
- **SEDPL** — EDPL with Vermeulen's (1993) sequence semantics: a variable
points to a stack of values, so reintroducing it shadows rather than clashes.
No novelty condition.
- **PLA** — Stack-based (de Bruijn) assignments. States are predicates of
stacks tagged with their common length.
- **PLASafe** — The same, with domain and extension tracked in the types, so
ill-formed updates are compile-time errors.

Each system provides static and dynamic interpretation functions. These are
equivalent in the PLA fragments and SEDPL given `merge`, and
Strawson-equivalent in EDPL and EEDPL given `/\` (`evalStatic` is total, but
`evalDyn` is not).

PLA, EDPL, EEDPL and SEDPL share their state operations through
`src/Shared.hs`.

## Build & run

Requires GHC 9.10 or later.

```bash
cabal build all
cabal run EDPL # or: EEDPL / SEDPL / PLA / PLASafe
cabal test
```

```bash
cabal repl # then, e.g., :m EEDPL
```
