# Lean formalization

A Lean 4 proof of the statement in the README of this repository:

```lean
theorem R4Embedding.closedOrientableSurfaceEmbedding :
    R4Embedding.ClosedOrientableSurfaceEmbeddingStatement
```

in `stage07/R4Initial/FinalTheorem.lean`. The statement says: for every compact Hausdorff smooth
surface `M` without boundary (any atlas, empty or disconnected surfaces included) that is
orientable, and every smooth Riemannian metric `g` on `M`, there is an injective smooth map
`F : M → ℝ⁴` with `⟪dF v, dF w⟫ = g(v, w)` for all tangent vectors.

The statement and every definition it uses are restated from Mathlib alone in
`comparator/Challenge.lean` (about 120 lines); that file is the one to read in order to check what is
proved. `R4Initial/StatementSanity.lean` shows that the hypotheses can be met (a closed orientable
surface carrying a smooth metric).

## Checking the proof

Lean `v4.34.1` and Mathlib `d13f23b` are pinned in `lean-toolchain` and `lake-manifest.json`.

```bash
lake exe cache get
lake build
lake env lean Verify.lean
```

`Verify.lean` reports that the final theorem depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`. The build compiles about 2,500 modules besides
Mathlib.

`comparator/config.json` is a configuration for
[Comparator](https://github.com/leanprover/comparator) (Linux), which checks that the theorem has
exactly the statement of `comparator/Challenge.lean` and replays the environment in the kernel.

## Contents

| Folder | Contents | License |
|---|---|---|
| `R4Embedding/`, `model_atlas/`, `stage07/R4Initial/`, `analytic/` | this proof | Apache-2.0 (repository `LICENSE`) |
| `upstream/` | the analytic construction of openai/math, commit `fd4aeeb2`, unchanged | Apache-2.0, `upstream/LICENSE` |
| `models_upstream/` | parts of qinz1yang/differential-geometry, commit `bafefb7` | Apache-2.0, `models_upstream/LICENSE`; changed files listed in `models_upstream/MODIFICATIONS.md` |
| `stage07/vendor/R4CoS/` | the classification of surfaces from LeanPool/lean-pool, commit `7c3ae77`, renamed | Apache-2.0, `LICENSE` and `NOTICE` there; see `stage07/VENDOR-CLASH.md` |

`RELEASE-MANIFEST.json` lists the SHA-256 of every file.
