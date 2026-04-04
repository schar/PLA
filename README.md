# PLA

Predicate Logic with Anaphora -- Haskell implementations of static and dynamic
first-order interpretations following Dekker
([1996](https://doi.org/10.1007/BF00628200),
[2002](https://doi.org/10.1023/A:1017575313451)).

Three perspectives:

- **EDPL** — Assignments as maps. States as sets of assignments tagged with a
common domain. Ill-formed updates rejected at runtime. Natural lattice structure
on states.
- **PLA** — Stack-based (de Bruijn) assignments. States are predicates of stacks
tagged with their common length. Ill-formed updates rejected at runtime.
- **PLASafe** — Stack-based assignments with type-level domain and extension
indices, ensuring well-formedness at compile time.

Each system provides static and dynamic interpretation functions. These are
equivalent in the PLA fragments and Strawson-equivalent in the EDPL fragment
(`evalStatic` is total, but `evalDPL` is not).

## Build & run

The `.cabal` file requires [GHC `9.6.7`](https://www.haskell.org/ghcup/), but
works up to `9.14.1`.

```bash
cabal build all
cabal run EDPL # or: PLA / PLASafe
```

```bash
cabal repl EDPL # or: PLA / PLASafe
```
