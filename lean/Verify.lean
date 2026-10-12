import R4Initial.FinalTheorem
import R4Initial.StatementSanity

/-! Run `lake env lean Verify.lean` after `lake build`.

The statement `ClosedOrientableSurfaceEmbeddingStatement` and every definition it uses are restated
from Mathlib alone in `comparator/Challenge.lean`. -/

/-- The complete statement, with no hypothesis left. -/
example : R4Embedding.ClosedOrientableSurfaceEmbeddingStatement.{0} :=
  R4Embedding.closedOrientableSurfaceEmbedding

#print axioms R4Embedding.closedOrientableSurfaceEmbedding

-- The hypotheses can be met: a closed orientable smooth surface carrying a smooth metric.
#print axioms R4Embedding.closedOrientableSurface_hypotheses_satisfiable
