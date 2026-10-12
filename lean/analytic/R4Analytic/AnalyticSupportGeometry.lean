import R4Embedding.CompactChartSupport
import R4Analytic.AnalyticPreparedGeometry
import OAI.Geometry.SurfaceImmersion.Primitive.PhasePrimitiveSupport
import Mathlib.Topology.Separation.Regular

/-! Apply the prepared coordinate geometry to the actual closed primitive
support. The explicit target condition on K is essential: membership in an
unrelated open S does not license an inverse of a partial homeomorphism.
These adapters are not a construction of the initial embedding. -/

noncomputable section
namespace R4Embedding

open Set Filter Manifold
open scoped ContDiff Topology
open OAI.ClosedSurfaceR4 OAI.ClosedSurfaceR4.FiniteOrderSmoothing
open OAI.ClosedSurfaceR4.SurfaceJetCoordinates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem analytic_phase_surface_support_eq_image (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {K : Set JetPolynomial.Base} (hK : IsCompact K) (hKt : K ⊆ e.target)
    (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    A.phaseSurfaceSupport i e K = (chart (i : M)).symm '' (e.symm '' K) := by
  apply compact_chart_support_eq_image (chart (i : M)) e hK hKt
  intro x hx
  obtain ⟨p, hp, rfl⟩ := hKA hx
  exact (chart (i : M)).map_source (A.weight_support i hp)

theorem analytic_phase_surface_support_coordinate (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {K : Set JetPolynomial.Base} (hK : IsCompact K) (hKt : K ⊆ e.target)
    (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    {p : M} (hp : p ∈ A.phaseSurfaceSupport i e K) :
    p ∈ (analyticPhaseChart A i e).source ∧
      ∃ q ∈ K, (analyticPhaseChart A i e) p = baseEquiv q := by
  have hKc : e.symm '' K ⊆ (chart (i : M)).target := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := hKA hx
    exact (chart (i : M)).map_source (A.weight_support i hr)
  obtain ⟨q, hq, heq, hs, hcoord⟩ :=
    compact_chart_support_coordinate (chart (i : M)) e hK hKt hKc hp
  refine ⟨⟨hs, Set.mem_univ _⟩, q, hq, ?_⟩
  exact congrArg baseEquiv hcoord

theorem analytic_phase_surface_support_in_outer_domain (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {K : Set JetPolynomial.Base} (hK : IsCompact K) (hKt : K ⊆ e.target)
    (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    (houter : ∀ p ∈ tsupport (A.weight i), A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {p : M} (hp : p ∈ A.phaseSurfaceSupport i e K) :
    (analyticPhaseChart A i e) p ∈ analyticPhaseOuterDomain A i e :=
  mem_chartConstantRegion_of_locally_constant _ _ _
    (analytic_phase_surface_support_coordinate A i e hK hKt hKA hp).1
    (houter p (A.phaseSurfaceSupport_subset_weight i e hKA hp))

/-- Select a compact profile neighbourhood before choosing the exact output.
Its interior contains K, and the actual coordinate germ holds on its entire
closure, including points outside the inner closed weight support. -/
theorem analytic_phase_profile_compact_neighborhood (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {K S : Set JetPolynomial.Base} (hK : IsCompact K) (hS : IsOpen S)
    (hKS : K ⊆ S) (hKt : K ⊆ e.target)
    (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    (houter : ∀ p ∈ tsupport (A.weight i), A.outer i =ᶠ[𝓝 p] (fun _ => 1)) :
    ∃ V : Set JetPolynomial.Base, IsOpen V ∧ K ⊆ V ∧ IsCompact (closure V) ∧
      closure V ⊆ S ∩ e.target ∧
      baseEquiv '' closure V ⊆ analyticPhaseOuterDomain A i e := by
  let D := (S ∩ e.target) ∩ baseEquiv ⁻¹' analyticPhaseOuterDomain A i e
  have hD : IsOpen D := (hS.inter e.open_target).inter
    ((analytic_phase_outer_domain_isOpen A i e).preimage baseEquiv.continuous)
  have hKD : K ⊆ D := by
    intro q hq
    have hw : e.symm q ∈ (A.chartWeightCompact i : Set JetPolynomial.Base) :=
      hKA ⟨q, hq, rfl⟩
    have hc : e.symm q ∈ (chart (i : M)).target := by
      obtain ⟨p, hp, heq⟩ := hw
      rw [← heq]
      exact (chart (i : M)).map_source (A.weight_support i hp)
    have ht : baseEquiv q ∈ (analyticPhaseChart A i e).target := by
      refine ⟨Set.mem_univ _, ?_, ?_⟩
      -- the inverse appears through `toHomeomorph.toOpenPartialHomeomorph`; restate it as
      -- `baseEquiv.symm` (definitionally equal) so that `symm_apply_apply` applies
      · change baseEquiv.symm (baseEquiv q) ∈ e.target
        simpa only [baseEquiv.symm_apply_apply] using hKt hq
      · change baseEquiv.symm (baseEquiv q) ∈ e.symm ⁻¹' (chart (i : M)).target
        simpa only [baseEquiv.symm_apply_apply, Set.mem_preimage] using hc
    refine ⟨⟨hKS hq, hKt hq⟩, ?_⟩
    apply analytic_phase_mem_outer_domain_on_closed_weight A i e houter ht
    simpa only [baseEquiv.symm_apply_apply] using hw
  obtain ⟨V, hV, hKV, hVD, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK hD hKD
  refine ⟨V, hV, hKV, hVc, fun q hq => (hVD hq).1, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  exact (hVD hq).2

theorem analytic_prepared_geometry_on_surface_support (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    {K : Set JetPolynomial.Base} (hK : IsCompact K) (hKt : K ⊆ e.target)
    (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    (houter : ∀ p ∈ tsupport (A.weight i), A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {U : Set (ℝ × ℝ)} (hKU : baseEquiv '' K ⊆ U)
    (hI : ∀ x ∈ U, Function.Injective (fderiv ℝ (A.phaseRealChartMap i e.symm F) x))
    (hHess : ∀ x ∈ U, 0 < PhaseGeometry.coordinateMetricHessian
      (RealModes.inducedCoordinateMetric (A.phaseRealChartMap i e.symm F))
      Prod.fst x SmallModes.dy SmallModes.dy)
    {p : M} (hp : p ∈ A.phaseSurfaceSupport i e K) :
    ∃ geometry : SmoothSurfaceProfileGeometry M p,
      geometry.chart = analyticPhaseChart A i e ∧
      geometry.u = coordinateSurfaceX (F ∘ (analyticPhaseChart A i e).symm) ∧
      geometry.v = coordinateSurfaceY (F ∘ (analyticPhaseChart A i e).symm) ∧
      geometry.acc = coordinateSurfaceYY (F ∘ (analyticPhaseChart A i e).symm) := by
  obtain ⟨hs, q, hq, hcoord⟩ :=
    analytic_phase_surface_support_coordinate A i e hK hKt hKA hp
  have hxU : (analyticPhaseChart A i e) p ∈ U := by
    rw [hcoord]
    exact hKU ⟨q, hq, rfl⟩
  exact analytic_prepared_phase_geometry_exists_on_outer_domain A i e hi hF hs
    (analytic_phase_surface_support_in_outer_domain A i e hK hKt hKA houter hp)
    (hI _ hxU) (hHess _ hxU)

end R4Embedding
