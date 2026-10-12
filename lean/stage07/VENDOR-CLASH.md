# The renamed copy of the classification of surfaces

`models_upstream/` contains the parts of qinz1yang/differential-geometry (commit `bafefb7`) used
here. That repository includes the Moise part of mccorvie/classification-of-surfaces under the
original declaration names (`LeanEval.Topology.ClassificationOfSurfaces...`). Lean Pool
(LeanPool/lean-pool, commit `7c3ae77`) contains the complete classification under the same names.

Lean merges duplicate imported theorems with identical types, but rejects duplicate definitions,
so the two cannot be loaded into one environment unchanged. The final theorem needs both: the
smoothing chart step uses differential-geometry, and the classification uses Lean Pool.

`stage07/vendor/R4CoS/` is therefore Lean Pool's `LeanPool/ClassificationOfSurfaces` with the
module prefix `LeanPool.ClassificationOfSurfaces` replaced by `R4CoS` and the identifier
`LeanEval` replaced by `R4CoS` outside import lines; nothing else is changed. `VENDOR.json` records
the SHA-256 of every source file and of its renamed copy. The license and notice are Lean Pool's.
