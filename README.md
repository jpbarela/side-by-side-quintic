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

## Blueprint

`blueprint/` holds a [leanblueprint](https://github.com/PatrickMassot/leanblueprint)
write-up of both proofs, with a dependency graph that tracks what is formalized.
Edit the chapters in `blueprint/src/chapters/`. Tag each result with its Lean name
(`\lean{...}`), add `\leanok` once it is stated or proved, and list dependencies
with `\uses{...}`.

The `Compile blueprint` workflow builds the project, the blueprint, the API docs and
the home page in `home_page/`, and checks that every Lean name in the blueprint exists.
It runs on pushes to `main` and deploys to GitHub Pages. In the repository settings,
set Pages → Source to "GitHub Actions" once.

To build locally (needs Python, a LaTeX distribution with `latexmk` and `xelatex`,
and graphviz):

```bash
pip install leanblueprint
leanblueprint pdf
leanblueprint web
leanblueprint checkdecls
leanblueprint serve
```

## Status

- [x] Shared statement (first draft)
- [x] Values of radical expressions lie in `solvableByRad`
- [x] Galois group of the generic quintic contains `S₅`; the Galois proof is complete
- [ ] Arnold: monodromy of roots, monodromy of radical expressions
- [ ] Bridge between algebraic values and analytic continuation
