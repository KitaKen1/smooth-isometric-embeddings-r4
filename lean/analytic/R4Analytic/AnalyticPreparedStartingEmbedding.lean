import R4Analytic.AnalyticAtlasC1Stability
import OAI.Geometry.SurfaceImmersion.Geometry.ReferenceBoundaryStartingFamily

/-! Apply the actual finite-point spherical preparation at a common
weighted C-one embedding budget. The scale and uniform constants are still
chosen before the cycles, crossing set and prepared map. This theorem
assumes the initial spherical embedding; it does not construct that input.
Pending compilation and transitive axiom audit. -/

noncomputable section
namespace R4Embedding

open Set Filter Manifold
open scoped ContDiff Topology
open OAI.ClosedSurfaceR4 OAI.ClosedSurfaceR4.FiniteOrderSmoothing

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem analytic_reference_circular_starting_embeddings (A : SmoothingAtlas M)
    (g : SmoothMetric M) {I : M → Space}
    (hI : ContMDiff planeModel spaceModel ∞ I) (hunit : ∀ p, ‖I p‖ = 1)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel I p))
    (hIinj : Function.Injective I) {η : ℝ} (hη : 0 < η) :
    ∃ r D c : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 ≤ D ∧ 0 < c ∧
      A.WeightedBound 1 2 D I ∧
      A.TensorWeightedBound 1 1 η (inducedTensor (r • I)) ∧
      (∀ p v, inducedForm (r • I) p v v ≤ (1/2 : ℝ)*g.inner p v v) ∧
      ∀ (n : ℕ) (B : SmoothingAtlas M) (d : CircularFamilyGeometry B (Fin n))
        (ε : ℝ), 0 < ε →
      ∃ (G : M → Space) (g₀ : SmoothMetric M) (normal : PreferredNormal (r • G)),
        ContMDiff planeModel spaceModel ∞ G ∧ (∀ p, ‖G p‖ = 1) ∧
        IsSmoothIsometricImmersion M g₀ (r • G) ∧
        Topology.IsClosedEmbedding (r • G) ∧
        g₀.inner = inducedTensor (r • G) ∧ Nonempty (MetricGoodPhaseData g₀ (r • G)) ∧
        normal.vector = (fun p => -G p) ∧
        A.WeightedBound 1 1 ε (G-I) ∧ A.WeightedBound 1 2 D G ∧
        (∀ p v, c*g.inner p v v ≤ g₀.inner p v v) ∧
        A.TensorWeightedBound 1 1 η g₀.inner ∧
        (∀ p v, g₀.inner p v v ≤ (1/2 : ℝ)*g.inner p v v) ∧
        FiniteBoundaryGeometry d.curves (boundaryCrossingSet d.curves univ) (r • G) normal := by
  obtain ⟨εembed, hεembed, hstable⟩ := analytic_initial_weighted_embedding_tolerance A hI hIinj hImm
  obtain ⟨r,D,c,hr,hr1,hD,hc,hIbound,hImetric,hIshort,hprepare⟩ :=
    A.reference_circular_starting_family g hI hunit hImm hη
  refine ⟨r,D,c,hr,hr1,hD,hc,hIbound,hImetric,hIshort,?_⟩
  intro n B d ε hε
  obtain ⟨G,g₀,normal,hG,hunitG,hisometry,hmetric,hgood,hnormal,hclose,hbound,
      hlower,hgmetric,hshort,hboundary⟩ :=
    hprepare n B d (min ε εembed) (lt_min hε hεembed)
  have hGclosed : Topology.IsClosedEmbedding G := hstable G hG
    (fun j => (hclose j).mono_const (min_le_right ε εembed))
  have hscaledinj : Function.Injective (r • G) := by
    intro p q hpq
    apply hGclosed.injective
    change r • G p = r • G q at hpq
    have hh := congrArg (fun v : Space => r⁻¹ • v) hpq
    simpa only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] using hh
  have hscaled : Topology.IsClosedEmbedding (r • G) :=
    hisometry.1.continuous.isClosedEmbedding hscaledinj
  refine ⟨G,g₀,normal,hG,hunitG,hisometry,hscaled,hmetric,hgood,hnormal,?_,
    hbound,hlower,hgmetric,hshort,hboundary⟩
  exact fun j => (hclose j).mono_const (min_le_left ε εembed)

end R4Embedding
