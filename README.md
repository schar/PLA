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
- **SEDPL** — EDPL over referent systems (Vermeulen 1993): a variable points to
a stack of values, so reintroducing it shadows rather than clashes. No
novelty condition.
- **PLA** — Stack-based (de Bruijn) assignments. States are predicates of
stacks tagged with their common length.
- **PLASafe** — The same, with domain and extension tracked in the types, so
ill-formed updates are compile-time errors.

Each system provides a dynamic interpretation `evalDyn` and a static one
`evalStatic`. In the PLA fragments they are equivalent given `merge`; in the
EDPL fragments, Strawson-equivalent given `/\` (`evalStatic` is total,
`evalDyn` is not). EEDPL and SEDPL add `evalStatic'`, exactly equivalent to
`evalDyn` given `merge`. EEDPL also has `evalStatic''`, a total variant with
Zeevat's symmetric merge that is Strawson-equivalent to `evalDyn`; the same
definition in SEDPL fails once a variable is reintroduced. What the four
value-level fragments share is in `src/Shared.hs`; PLASafe stands alone.

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
