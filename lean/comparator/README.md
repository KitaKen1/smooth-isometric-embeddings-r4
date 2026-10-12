# Comparator configuration

`Challenge.lean` states the complete target from Mathlib alone: the definitions of the plane, of
four-space, of smooth metrics, of isometric embeddings and of orientability are copied verbatim from
`R4Embedding/Problem.lean`, `R4Embedding/SurfaceOrientation.lean` and
`R4Embedding/MainStatement.lean`, and the theorem is closed by `sorry` (the challenge format).

[Comparator](https://github.com/leanprover/comparator) checks that the solution theorem
`R4Embedding.closedOrientableSurfaceEmbedding` (module `R4Initial.FinalTheorem`) has the same
statement, that every declaration the statement uses is identical in the solution environment, that
only `propext`, `Classical.choice` and `Quot.sound` are used, and replays the solution environment
in the kernel (`config-nanoda.json` also runs the nanoda kernel).

The challenge module has to be a library of the workspace in which Comparator runs, for example:

```toml
[[lean_lib]]
name = "Challenge"
srcDir = "comparator"
```

Comparator's sandbox (landrun) requires Linux.
