# Statement in the format of Formal Conjectures

[SmoothIsometricEmbeddingR4.lean](SmoothIsometricEmbeddingR4.lean) asks whether every
closed orientable smooth surface with any smooth Riemannian metric admits a smooth
isometric embedding into four-space. It records the affirmative answer as `answer(True)`.

- [Complete Lean proof of this target](../lean/FCSolution.lean).
- [Original R4 theorem](../lean/stage07/R4Initial/FinalTheorem.lean).

The file defines only orientability and writes the Euclidean spaces, smooth metric,
smoothness, injectivity and metric preservation directly in the theorem.
It contains a `by sorry` statement with an
external `formal_proof` link, following the Bapat example. `COMMIT` will be replaced
after publication. The draft has not been submitted to FC. The private CI run for this target
passed; the public main CI is pending.

The orientability definition is extracted into [FCTargetDefinitions.lean](../lean/FCTargetDefinitions.lean).
The external proof writes `True` for FC's annotated `answer(True)`.
See [verification](../comparator/README.md) for the local checks and remaining CI work.
