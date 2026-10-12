import R4Analytic.AnalyticCircularSequence
import OAI.Geometry.SurfaceImmersion.Primitive.CircularPrefixMetrics

/-! Realize the concrete prefix metrics by the embedding-preserving sequence.
Initial embedding and prepared convexity/boundary data are explicit inputs.
Pending compilation and transitive axiom audit. -/

noncomputable section
namespace R4Embedding
open OAI.ClosedSurfaceR4 OAI.ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open scoped ContDiff Topology
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
variable {B : SmoothingAtlas M} {N : ℕ}
theorem analytic_circular_total_embedding (d : CircularPrimitiveFamily B (Fin N)) (g h : SmoothMetric M)
    (htarget : h.inner = g.inner+d.totalTensor)
    (hconvex : ∀ a : Fin N, d.ConvexMetric (d.prefixMetric g a.castSucc) a)
    {F : M → Space} (n : PreferredNormal F) (hF : IsSmoothIsometricEmbedding g F)
    (data : MetricGoodPhaseData g F)
    (hgeom : FiniteBoundaryGeometry d.curves (boundaryCrossingSet d.curves univ) F n) :
    ∃ W : M → Space, IsSmoothIsometricEmbedding h W ∧ Nonempty (MetricGoodPhaseData h W) := by
  have hstart : d.prefixMetric g 0 = g := d.prefixMetric_zero g
  have hend : d.prefixMetric g (Fin.last N) = h :=
    metric_eq_of_inner_eq ((d.prefixMetric_last g).trans htarget.symm)
  have hF' : IsSmoothIsometricEmbedding (d.prefixMetric g 0) F := by rwa [hstart]
  have hdata : MetricGoodPhaseData (d.prefixMetric g 0) F := by rwa [hstart]
  obtain ⟨W,hW,hgood,_⟩ := analytic_circular_sequence_embeddings N d (d.prefixMetric g)
    (d.prefixMetric_step g) hconvex F n hF' hdata hgeom
  rw [hend] at hW hgood
  exact ⟨W,hW,hgood⟩

end R4Embedding
