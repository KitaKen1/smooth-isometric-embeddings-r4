import R4Embedding.Problem
import OAI.Geometry.Immersion.ClosedSurface.MetricModel

/-! The upstream isometry predicate uses the same standard smooth metric
and the same tangent inner products as the local specification. -/

noncomputable section
namespace R4Embedding

open scoped ContDiff
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem analytic_isometry_iff_local_spec {g : SmoothMetric M} {F : M → Space} :
    OAI.ClosedSurfaceR4.IsSmoothIsometricImmersion M g F ↔ IsSmoothIsometricMap g F :=
  Iff.rfl

end R4Embedding
