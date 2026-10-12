import R4Analytic.AnalyticSupportGeometry
import R4Analytic.AnalyticOrdinaryGeometry
import R4Embedding.RestrictedProfileAtlas
import R4Embedding.PrimitiveTolerances

/-! Assemble genuine phase and exterior charts before selecting the output.
The perturbation atlas is explicit and may differ from the correction
atlas stored in MetricGoodPhaseData. All constants, compact chart balls
and position tolerances come from the old
embedding and the target metric. The output estimates used below are exactly
the first profiles and slow/correction bounds retained by the primitive
adapter, on one and the same W. -/

noncomputable section
namespace R4Embedding

open Set Filter Manifold
open scoped ContDiff Topology BigOperators
open OAI.ClosedSurfaceR4 OAI.ClosedSurfaceR4.FiniteOrderSmoothing
open OAI.ClosedSurfaceR4.SurfaceJetCoordinates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

def analyticPhaseProfileDomain (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (Vprofile : Set JetPolynomial.Base) : Set (ℝ × ℝ) :=
  analyticPhaseOuterDomain A i e ∩ baseEquiv.symm ⁻¹' Vprofile

structure AnalyticPrimitivePatch {g : SmoothMetric M} {F : M → Space}
    (A : SmoothingAtlas M)
    (hOld : IsSmoothIsometricMap g F)
    (i : A.centers) (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (K Vprofile : Set JetPolynomial.Base) (p : M) where
  geometry : SmoothSurfaceProfileGeometry M p
  domain : Set (ℝ × ℝ)
  domain_open : IsOpen domain
  mem_domain : geometry.chart p ∈ domain
  description :
    (geometry.chart = analyticPhaseChart A i e ∧
      geometry.u = coordinateSurfaceX (F ∘ (analyticPhaseChart A i e).symm) ∧
      geometry.v = coordinateSurfaceY (F ∘ (analyticPhaseChart A i e).symm) ∧
      geometry.acc = coordinateSurfaceYY (F ∘ (analyticPhaseChart A i e).symm) ∧
      domain = analyticPhaseProfileDomain A i e Vprofile) ∨
    ∃ j : A.centers, ∃ hp : p ∈ (coordinateChart (j : M)).source,
      geometry = analyticOrdinaryGeometry hOld (j : M) hp ∧
      domain = analyticExteriorDomain A j (A.phaseSurfaceSupport i e K)

theorem analytic_primitive_patches_exist {g : SmoothMetric M} {F : M → Space}
    (A : SmoothingAtlas M)
    (houter : ∀ i x, x ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hOld : IsSmoothIsometricMap g F)
    (i : A.centers) (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm)
    {K : Set JetPolynomial.Base} (hK : IsCompact K) (hKt : K ⊆ e.target)
    (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    {U : Set (ℝ × ℝ)} (hKU : baseEquiv '' K ⊆ U)
    (hI : ∀ x ∈ U, Function.Injective (fderiv ℝ (A.phaseRealChartMap i e.symm F) x))
    (hHess : ∀ x ∈ U, 0 < PhaseGeometry.coordinateMetricHessian
      (RealModes.inducedCoordinateMetric (A.phaseRealChartMap i e.symm F))
      Prod.fst x SmallModes.dy SmallModes.dy)
    {Vprofile : Set JetPolynomial.Base} (hVprofile : IsOpen Vprofile) (hKV : K ⊆ Vprofile)
    (p : M) : Nonempty (AnalyticPrimitivePatch A hOld i e K Vprofile p) := by
  classical
  by_cases hp : p ∈ A.phaseSurfaceSupport i e K
  · obtain ⟨geometry, hchart, hu, hv, hacc⟩ :=
      analytic_prepared_geometry_on_surface_support A i e hi hOld.1 hK hKt hKA
        (houter i) hKU hI hHess hp
    have hd : IsOpen (analyticPhaseProfileDomain A i e Vprofile) :=
      (analytic_phase_outer_domain_isOpen A i e).inter
        (hVprofile.preimage baseEquiv.symm.continuous)
    have hm : geometry.chart p ∈ analyticPhaseProfileDomain A i e Vprofile := by
      rw [hchart]
      refine ⟨analytic_phase_surface_support_in_outer_domain A i e hK hKt hKA
        (houter i) hp, ?_⟩
      obtain ⟨_, q, hq, hcoord⟩ := analytic_phase_surface_support_coordinate A i e hK hKt hKA hp
      rw [hcoord, Set.mem_preimage, baseEquiv.symm_apply_apply]
      exact hKV hq
    exact ⟨⟨geometry, _, hd, hm, Or.inl ⟨hchart, hu, hv, hacc, rfl⟩⟩⟩
  · obtain ⟨j, hs, hm⟩ := analytic_exterior_domains_cover A hp
    exact ⟨⟨analyticOrdinaryGeometry hOld (j : M) hs, _,
      analytic_exterior_domain_isOpen A j isClosed_closure,
      hm, Or.inr ⟨j, hs, rfl, rfl⟩⟩⟩

theorem AnalyticPrimitivePatch.profiles_from_output {g : SmoothMetric M} {F : M → Space}
    {A : SmoothingAtlas M} {hOld : IsSmoothIsometricMap g F}
    {i : A.centers} {e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base}
    (houter : ∀ j x, x ∈ tsupport (A.weight j) → A.outer j =ᶠ[𝓝 x] (fun _ => 1))
    (hi : ContDiff ℝ ∞ e.symm) {K Vprofile : Set JetPolynomial.Base} {p : M}
    (patch : AnalyticPrimitivePatch A hOld i e K Vprofile p) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ r : ℝ,
      Metric.closedBall (patch.geometry.chart p) r ⊆ patch.geometry.chart.target ∩ patch.domain →
      ∀ (G V W : M → Space), ContMDiff planeModel spaceModel ∞ G →
      ContMDiff planeModel spaceModel ∞ V → ContMDiff planeModel spaceModel ∞ W →
      ∀ a c : ℝ, 0 ≤ a → 0 ≤ c →
      (∀ q ∈ closure Vprofile, AnalyticFirstProfileEstimate
        (A.phaseRealChartMap i e.symm F) (A.phaseRealChartMap i e.symm W) (baseEquiv q) a) →
      A.WeightedBound 1 3 a (G-F) → A.WeightedBound 1 2 c (W-V) →
      (∀ y ∉ A.phaseSurfaceSupport i e K, V =ᶠ[𝓝 y] G) →
      patch.geometry.HasFirstProfiles r (2*(D*(a+c))) W := by
  rcases patch.description with ⟨hchart, hu, hv, hacc, hdomain⟩ | ⟨j, hp, hgeometry, hdomain⟩
  · refine ⟨1, le_rfl, ?_⟩
    intro r hr G V W hG hV hW a c ha hc hphase hslow hcorrection hexterior
    have hraw := analytic_raw_profiles_of_phase_profiles_on_outer_domain A i e hi
      hOld.1 hW patch.geometry hchart hu hv hacc
      (fun q hq => by
        have hqD := (hr (Metric.ball_subset_closedBall hq)).2
        rw [hdomain] at hqD
        exact hqD.1)
      (fun q hq => by
        have hqD := (hr (Metric.ball_subset_closedBall hq)).2
        rw [hdomain] at hqD
        simpa only [baseEquiv.apply_symm_apply] using
          hphase (baseEquiv.symm q) (subset_closure hqD.2))
    exact hraw.toFirstProfiles.mono (by nlinarith)
  · obtain ⟨D, hD, hd⟩ := analytic_exterior_profiles_of_atlas_bounds A houter hOld j hp
      (A.phaseSurfaceSupport i e K)
    refine ⟨D+1, by linarith, ?_⟩
    intro r hr G V W hG hV hW a c ha hc hphase hslow hcorrection hexterior
    rw [hgeometry]
    have hbound := hd G V W hG hV hW a c ha hc hslow hcorrection hexterior r (by
      -- the chart of `analyticOrdinaryGeometry` is `coordinateChart j` by definition, which the
      -- final syntactic check of `simpa` does not see
      have h := hr
      simp only [hgeometry, hdomain] at h
      exact h)
    exact hbound.mono (by nlinarith)

/-- The complete finite atlas application to the actual primitive estimates.
This implication asserts no existence of the future output: that existence
is supplied separately by the preserving construction. -/
theorem analytic_primitive_embedding_tolerance {g : SmoothMetric M} {F : M → Space}
    (A : SmoothingAtlas M)
    (houter : ∀ i x, x ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hOld : IsSmoothIsometricMap g F)
    (hFinj : Function.Injective F) (h : SmoothMetric M)
    (i : A.centers) (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm)
    {K : Set JetPolynomial.Base} (hK : IsCompact K) (hKt : K ⊆ e.target)
    (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    {U : Set (ℝ × ℝ)} (hKU : baseEquiv '' K ⊆ U)
    (hI : ∀ x ∈ U, Function.Injective (fderiv ℝ (A.phaseRealChartMap i e.symm F) x))
    (hHess : ∀ x ∈ U, 0 < PhaseGeometry.coordinateMetricHessian
      (RealModes.inducedCoordinateMetric (A.phaseRealChartMap i e.symm F))
      Prod.fst x SmallModes.dy SmallModes.dy)
    {Vprofile : Set JetPolynomial.Base} (hVprofile : IsOpen Vprofile) (hKV : K ⊆ Vprofile) :
    ∃ δ ζ η : ℝ, 0 < δ ∧ 0 < ζ ∧ 0 < η ∧ ∀ (z : ℝ), 0 < z → z < ζ → z ≤ 1 →
      ∀ (G V W : M → Space), ContMDiff planeModel spaceModel ∞ G →
      ContMDiff planeModel spaceModel ∞ V → IsSmoothIsometricMap h W →
      (∀ q ∈ closure Vprofile, AnalyticFirstProfileEstimate
        (A.phaseRealChartMap i e.symm F) (A.phaseRealChartMap i e.symm W) (baseEquiv q) δ) →
      A.WeightedBound 1 3 δ (G-F) → A.WeightedBound 1 2 (z^8) (W-V) →
      (∀ y ∉ A.phaseSurfaceSupport i e K, V =ᶠ[𝓝 y] G) →
      (∀ y, dist (W y) (F y) < η) → Topology.IsClosedEmbedding W := by
  classical
  let patch : ∀ p : M, AnalyticPrimitivePatch A hOld i e K Vprofile p :=
    fun p => Classical.choice (analytic_primitive_patches_exist A houter hOld i e hi hK hKt hKA
      hKU hI hHess hVprofile hKV p)
  obtain ⟨centers, r, ε, η, hε, hη, hr, hcover, htol⟩ :=
    exists_closed_embedding_tolerance_of_metric_profiles_in_open h
      (fun p => (patch p).geometry) (fun p => (patch p).domain)
      (fun p => (patch p).domain_open) (fun p => (patch p).mem_domain)
      hOld.1.continuous hFinj
  choose D hD hd using (fun p => (patch p).profiles_from_output houter hi)
  let Dtotal := 1 + ∑ p ∈ centers, D p
  have hDn : ∀ p, 0 ≤ D p := fun p => le_trans (by norm_num) (hD p)
  have hsum : 0 ≤ ∑ p ∈ centers, D p := Finset.sum_nonneg (fun p _ => hDn p)
  have hDt : 0 < Dtotal := by dsimp [Dtotal]; linarith
  have hDb : ∀ p ∈ centers, D p ≤ Dtotal := by
    intro p hp
    have hb := Finset.single_le_sum (fun q _ => hDn q) hp
    dsimp [Dtotal]
    linarith
  let δ := ε/(4*Dtotal)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hDt)
  refine ⟨δ, min 1 δ, η, hδ, lt_min (by norm_num) hδ, hη, ?_⟩
  intro z hz hzζ hz1 G V W hG hV hW hphase hslow hcorrection hexterior hposition
  apply htol W hW _ hposition
  intro p hp
  have hDp : 0 ≤ D p := hDn p
  apply (hd p (r p) (hr p).2 G V W hG hV hW.1 δ (z^8) hδ.le
    (pow_nonneg hz.le _) hphase hslow hcorrection hexterior).mono
  exact primitive_first_profile_budget hε hDt hDp (hDb p hp) rfl hz.le hzζ

end R4Embedding
