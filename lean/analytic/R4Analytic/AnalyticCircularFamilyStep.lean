import R4Analytic.AnalyticCircularBoundaryRemoval
import OAI.Geometry.SurfaceImmersion.Primitive.CircularPrimitiveFamily

/-! Strengthen the actual finite circular family step with injectivity.
Pending compilation and transitive axiom audit. -/

noncomputable section
namespace R4Embedding
open OAI.ClosedSurfaceR4 OAI.ClosedSurfaceR4.FiniteOrderSmoothing
open Set Filter Manifold
open scoped ContDiff Topology
open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
variable {B : SmoothingAtlas M} {ι : Type*} [Fintype ι]
theorem analytic_circular_family_embedding_step [DecidableEq ι] (d : CircularPrimitiveFamily B ι) (a : ι)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F) (hFinj : Function.Injective F)
    (n : PreferredNormal F) (hgeom : FiniteBoundaryGeometry d.curves (boundaryCrossingSet d.curves univ) F n)
    (hconvex : ∀ p ∈ tsupport (B.weight (d.curves a).index),
      ‖coordinateChart ((d.curves a).index : M) p-coordinateChart ((d.curves a).index : M) (d.curves a).index‖ ≤ d.chartRadius a →
      ∀ v : Base, v ≠ 0 → 0 < coordinateMetricHessian (coordinateMetric g ((d.curves a).index : M))
        (centeredConvexPhase (d.linearPart a) (d.convexPart a)
          (coordinateChart ((d.curves a).index : M) (d.curves a).index))
        (coordinateChart ((d.curves a).index : M) p) v v)
    (data : MetricGoodPhaseData g F) (h : SmoothMetric M)
    (htarget : h.inner = g.inner + (fun p => (d.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d.phase a) p)) :
    ∀ ηpos : ℝ, 0 < ηpos →
    ∃ W : M → Space, IsSmoothIsometricEmbedding h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      (∀ p, dist (W p) (F p) < ηpos) ∧
      ∃ N : PreferredNormal W,
        FiniteBoundaryGeometry (fun j : {j : ι // j ≠ a} => d.curves j)
          (boundaryCrossingSet (fun j : {j : ι // j ≠ a} => d.curves j) univ) W N := by
  intro ηpos hηpos
  apply analytic_circular_boundary_removal_embedding_step d.curves a d.radius d.outerRadius d.chartRadius
    d.radius_pos (d.radius_outer a) (d.radius_chart a) (d.weight_positive a) d.region d.carrier d.cover
    d.linearPart d.convexPart d.first_coordinate d.pair_finite d.triple_empty
    (d.tangencies_finite a) ?_ hF hFinj n hgeom hconvex (d.amplitude_smooth a)
    (d.amplitude_nonneg a) (d.amplitude_positive a) (d.phase_germ a) data h htarget ηpos hηpos
  intro j k hjk p hp hj hk
  apply d.independent j k hjk p _ hj hk
  rwa [boundaryCrossingSet_eq_circular d.curves d.radius d.carrier]

end R4Embedding
