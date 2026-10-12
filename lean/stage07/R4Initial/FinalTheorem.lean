import R4Initial.Stage07Final
import R4Analytic.AnalyticFinalReduction

/-! The complete target, with no hypothesis left (stage 10).

Every closed orientable smooth surface, with its own atlas and any smooth Riemannian metric (empty
and disconnected surfaces included), has a C∞ isometric embedding into `ℝ⁴`. Stage 07 supplies the
initial `ℝ³` embedding of every such surface (classification, genus, smoothing:
`closed_statement_of_analytic`), and the analytic construction turns any initial `ℝ³` embedding into
an isometric embedding into `ℝ⁴` (`analytic_isometric_embedding_from_three_statement`).

This module imports the whole analytic chain and its upstream closure. Build it by name
(`lake build R4Initial.FinalTheorem`) only after the staged upstream build has finished; do not build
the `R4Initial` library as a whole while the staged build is running. -/

noncomputable section
namespace R4Embedding

universe u

/-- Every closed orientable smooth Riemannian surface embeds isometrically and smoothly in `ℝ⁴`. -/
theorem closedOrientableSurfaceEmbedding : ClosedOrientableSurfaceEmbeddingStatement.{u} :=
  closed_statement_of_analytic analytic_isometric_embedding_from_three_statement

end R4Embedding
