# Files changed from qinz1yang/differential-geometry

The files below differ from commit `bafefb7ce5ce7e40417641d67e6e95727b7bba1f` only to compile with
Lean 4.34.1 and Mathlib `d13f23b` (the upstream repository uses a later Mathlib): two lemma renames
(`IsLocalDiffeomorphAt.contMDiffAt_localInverse` is `localInverse_contMDiffAt` there, and
`IsImmersion(At).mfderiv_injective` is `injective_mfderiv`) and two proofs closed by `rfl`, because
`mfderiv_eq_fderiv` does not insert `fromTangentSpace` in that Mathlib. No statement is changed.
All other files are unchanged copies.

- `DifferentialGeometry/Topology/Embedding/Factor.lean`
- `DifferentialGeometry/Topology/Manifold/AddCircle/Descent.lean`
- `DifferentialGeometry/Topology/Manifold/AddCircle/ParameterDerivative.lean`
- `DifferentialGeometry/Topology/Manifold/AddCircle/SmoothEmbedding.lean`
- `DifferentialGeometry/Topology/Manifold/ImmersionDifferential.lean`
- `DifferentialGeometry/Topology/Manifold/Interval/Immersion.lean`
- `DifferentialGeometry/Topology/Manifold/LocalDiffeomorph/Determinant.lean`
- `DifferentialGeometry/Topology/Manifold/LocalDiffeomorph/PartialDiffeomorph.lean`
- `DifferentialGeometry/Topology/Manifold/OpenEmbedding.lean`
- `DifferentialGeometry/Topology/Manifold/Quotient.lean`
- `DifferentialGeometry/Topology/Manifold/RegularLevel/Tangent.lean`
- `DifferentialGeometry/Topology/PlanarJordan/RegularCurve.lean`
