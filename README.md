# Two proofs of the unsolvability of the quintic

A Lean 4 / Mathlib project proving one statement, `Quintic.QuinticUnsolvable`
(in `Quintic/Statement.lean`), in two ways:

- `Quintic/Galois.lean`: via Galois theory and Mathlib's `solvableByRad`.
- `Quintic/Arnold.lean`: via Arnold's monodromy argument.

`Quintic.lean` combines both, so Lean checks they prove the same proposition.

## Getting started

1. Push this folder to a public GitHub repo.
2. Open it in a Codespace (Code → Codespaces), or clone locally with
   [elan](https://github.com/leanprover/elan) installed.
3. Run `lake update` once and commit the generated `lake-manifest.json`.
4. Run `lake exe cache get` (downloads prebuilt Mathlib), then `lake build`.

Pinned to Mathlib `v4.35.0` with Lean `v4.35.0`. To upgrade, change both
`lean-toolchain` and `rev` in `lakefile.toml`, then `lake update`.

## Status

- [x] Shared statement (first draft)
- [x] Values of radical expressions lie in `solvableByRad`
- [ ] Galois group of the generic quintic is `S₅`
- [ ] Arnold: monodromy of roots, monodromy of radical expressions
- [ ] Bridge between algebraic values and analytic continuation
