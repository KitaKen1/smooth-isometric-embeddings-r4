import R4Analytic.AnalyticClosedWeightCoordinates
import OAI.Geometry.SurfaceImmersion.Geometry.MetricConnectionNaturality
import OAI.Geometry.SurfaceImmersion.Geometry.SecondFormNormalFields

/-! The prepared positive phase Hessian supplies the local Gauss coefficient.
All first and second fields below are derivatives of the actual old map F.
The initial embedding and the preparation itself are not supplied here. -/

noncomputable section
namespace R4Embedding

open Set Filter Manifold
open scoped ContDiff Topology Matrix
open OAI.ClosedSurfaceR4 OAI.ClosedSurfaceR4.FiniteOrderSmoothing
open OAI.ClosedSurfaceR4.SurfaceJetCoordinates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

theorem analytic_phase_chart_inverse_smooth (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) :
    ContMDiffOn pairModel planeModel ∞ (analyticPhaseChart A i e).symm
      (analyticPhaseChart A i e).target := by
  have hc := (OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chart_symm_smooth (i : M)).comp
    (hi.comp baseEquiv.symm.contDiff).contMDiff.contMDiffOn
    (fun x (hx : x ∈ (analyticPhaseChart A i e).target) => hx.2.2)
  exact hc

theorem analytic_phase_coordinate_derivative_injective_of_germ (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {x : ℝ × ℝ}
    (hg : A.phaseRealChartMap i e.symm F =ᶠ[𝓝 x]
      rawToSpace.symm ∘ F ∘ (analyticPhaseChart A i e).symm)
    (hI : Function.Injective (fderiv ℝ (A.phaseRealChartMap i e.symm F) x)) :
    Function.Injective (fderiv ℝ (F ∘ (analyticPhaseChart A i e).symm) x) := by
  have hfirst := (coordinate_first_and_yy_of_raw_germ
    (A.phaseRealChartMap_smooth i hi hF) hg).1
  intro v w hvw
  apply hI
  rw [hfirst v, hfirst w, hvw]

theorem analytic_phase_coordinate_derivative_injective (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {x : ℝ × ℝ}
    (hx : A.chartWeight i (e.symm (baseEquiv.symm x)) ≠ 0)
    (hI : Function.Injective (fderiv ℝ (A.phaseRealChartMap i e.symm F) x)) :
    Function.Injective (fderiv ℝ (F ∘ (analyticPhaseChart A i e).symm) x) :=
  analytic_phase_coordinate_derivative_injective_of_germ A i e hi hF
    (analytic_phase_raw_germ A i e hi F hx) hI

theorem analytic_phase_gauss_certificate_of_germ (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {x : ℝ × ℝ}
    (hg : A.phaseRealChartMap i e.symm F =ᶠ[𝓝 x]
      rawToSpace.symm ∘ F ∘ (analyticPhaseChart A i e).symm)
    (hI : Function.Injective (fderiv ℝ (A.phaseRealChartMap i e.symm F) x))
    (hHess : 0 < PhaseGeometry.coordinateMetricHessian
      (RealModes.inducedCoordinateMetric (A.phaseRealChartMap i e.symm F))
      Prod.fst x SmallModes.dy SmallModes.dy) :
    ∃ k l : ℝ, ∃ normal : Space,
      coordinateSurfaceYY (F ∘ (analyticPhaseChart A i e).symm) x =
        k • coordinateSurfaceX (F ∘ (analyticPhaseChart A i e).symm) x +
        l • coordinateSurfaceY (F ∘ (analyticPhaseChart A i e).symm) x + normal ∧
      k ≠ 0 ∧
      inner ℝ (coordinateSurfaceX (F ∘ (analyticPhaseChart A i e).symm) x) normal = 0 ∧
      inner ℝ (coordinateSurfaceY (F ∘ (analyticPhaseChart A i e).symm) x) normal = 0 := by
  let G := A.phaseRealChartMap i e.symm F
  let Gamma := PhaseGeometry.metricConnectionAt
    (RealModes.inducedCoordinateMetric G x, fderiv ℝ (RealModes.inducedCoordinateMetric G) x)
  let k := (Gamma 2).1
  let l := (Gamma 2).2
  let N := RealModes.realSecondForm G SmallModes.dy SmallModes.dy x
  have hG : ContDiff ℝ ∞ G := A.phaseRealChartMap_smooth i hi hF
  obtain ⟨hfirst,hsecond⟩ := coordinate_first_and_yy_of_raw_germ hG hg
  have hD : NormalFrame.gramDet (SmallModes.coordDeriv SmallModes.dx G x)
      (SmallModes.coordDeriv SmallModes.dy G x) ≠ 0 :=
    RealModes.gramDet_ne_zero_of_injective _ hI
  have hdecomposition := RealModes.second_connection_decomposition hG x SmallModes.dy SmallModes.dy
  have hraw : SmallModes.coordDeriv SmallModes.dy (SmallModes.coordDeriv SmallModes.dy G) x =
      k • SmallModes.coordDeriv SmallModes.dx G x +
      l • SmallModes.coordDeriv SmallModes.dy G x + N := by
    have hconnection : PhaseGeometry.connectionContract Gamma SmallModes.dy SmallModes.dy =
        Gamma 2 := by simp [PhaseGeometry.connectionContract, SmallModes.dy]
    change _ = fderiv ℝ G x
      (PhaseGeometry.connectionContract Gamma SmallModes.dy SmallModes.dy) + N at hdecomposition
    rw [hconnection] at hdecomposition
    change _ = SmallModes.coordDeriv (Gamma 2) G x + N at hdecomposition
    -- expand only the connection term on the right (an unapplied rewrite hits the left side first)
    rw [RealModes.coordDeriv_eq_basis G (Gamma 2) x] at hdecomposition
    exact hdecomposition
  have hnegative : k < 0 := by
    rw [PhaseGeometry.coordinateMetricHessian_fst_dy] at hHess
    change 0 < -k at hHess
    linarith
  have hX : rawToSpace (SmallModes.coordDeriv SmallModes.dx G x) =
      coordinateSurfaceX (F ∘ (analyticPhaseChart A i e).symm) x := by
    simpa only [SmallModes.coordDeriv, SmallModes.dx, coordinateSurfaceX,
      ContinuousLinearEquiv.apply_symm_apply] using
      congrArg rawToSpace (hfirst (1, 0))
  have hY : rawToSpace (SmallModes.coordDeriv SmallModes.dy G x) =
      coordinateSurfaceY (F ∘ (analyticPhaseChart A i e).symm) x := by
    simpa only [SmallModes.coordDeriv, SmallModes.dy, coordinateSurfaceY,
      ContinuousLinearEquiv.apply_symm_apply] using
      congrArg rawToSpace (hfirst (0, 1))
  have hYY : rawToSpace
      (SmallModes.coordDeriv SmallModes.dy (SmallModes.coordDeriv SmallModes.dy G) x) =
      coordinateSurfaceYY (F ∘ (analyticPhaseChart A i e).symm) x := by
    -- `SmallModes.coordDeriv dy G` occurs unapplied inside `fderiv`, where `simp` cannot unfold it;
    -- the two sides agree by definition
    have h := congrArg rawToSpace hsecond
    simp only [ContinuousLinearEquiv.apply_symm_apply] at h
    exact h
  obtain ⟨hNX, hNY⟩ := GeometryPreservation.realSecondForm_field_perp hD SmallModes.dy SmallModes.dy
  refine ⟨k, l, rawToSpace N, ?_, ne_of_lt hnegative, ?_, ?_⟩
  · have h := congrArg rawToSpace hraw
    simpa only [map_add, map_smul, hX, hY, hYY] using h
  · simpa only [hX] using rawToSpace_orthogonal hNX
  · simpa only [hY] using rawToSpace_orthogonal hNY

theorem analytic_phase_gauss_certificate (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {x : ℝ × ℝ}
    (hx : A.chartWeight i (e.symm (baseEquiv.symm x)) ≠ 0)
    (hI : Function.Injective (fderiv ℝ (A.phaseRealChartMap i e.symm F) x))
    (hHess : 0 < PhaseGeometry.coordinateMetricHessian
      (RealModes.inducedCoordinateMetric (A.phaseRealChartMap i e.symm F))
      Prod.fst x SmallModes.dy SmallModes.dy) :
    ∃ k l : ℝ, ∃ normal : Space,
      coordinateSurfaceYY (F ∘ (analyticPhaseChart A i e).symm) x =
        k • coordinateSurfaceX (F ∘ (analyticPhaseChart A i e).symm) x +
        l • coordinateSurfaceY (F ∘ (analyticPhaseChart A i e).symm) x + normal ∧
      k ≠ 0 ∧
      inner ℝ (coordinateSurfaceX (F ∘ (analyticPhaseChart A i e).symm) x) normal = 0 ∧
      inner ℝ (coordinateSurfaceY (F ∘ (analyticPhaseChart A i e).symm) x) normal = 0 :=
  analytic_phase_gauss_certificate_of_germ A i e hi hF
    (analytic_phase_raw_germ A i e hi F hx) hI hHess

theorem analytic_prepared_phase_geometry_exists (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {p : M}
    (hp : p ∈ (analyticPhaseChart A i e).source)
    (hx : A.chartWeight i (e.symm (baseEquiv.symm ((analyticPhaseChart A i e) p))) ≠ 0)
    (hI : Function.Injective (fderiv ℝ (A.phaseRealChartMap i e.symm F)
      ((analyticPhaseChart A i e) p)))
    (hHess : 0 < PhaseGeometry.coordinateMetricHessian
      (RealModes.inducedCoordinateMetric (A.phaseRealChartMap i e.symm F))
      Prod.fst ((analyticPhaseChart A i e) p) SmallModes.dy SmallModes.dy) :
    ∃ data : SmoothSurfaceProfileGeometry M p,
      data.chart = analyticPhaseChart A i e ∧
      data.u = coordinateSurfaceX (F ∘ (analyticPhaseChart A i e).symm) ∧
      data.v = coordinateSurfaceY (F ∘ (analyticPhaseChart A i e).symm) ∧
      data.acc = coordinateSurfaceYY (F ∘ (analyticPhaseChart A i e).symm) := by
  obtain ⟨k,l,normal,hgauss,hk,hnu,hnv⟩ :=
    analytic_phase_gauss_certificate A i e hi hF hx hI hHess
  let data := geometryOfCoordinateSurface hF (analyticPhaseChart A i e)
    (analytic_phase_chart_inverse_smooth A i e hi) hp
    (analytic_phase_coordinate_derivative_injective A i e hi hF hx hI)
    normal k l hgauss hk hnu hnv
  exact ⟨data, rfl, rfl, rfl, rfl⟩

theorem analytic_prepared_phase_geometry_exists_on_outer_domain
    (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {p : M}
    (hp : p ∈ (analyticPhaseChart A i e).source)
    (hx : (analyticPhaseChart A i e) p ∈ analyticPhaseOuterDomain A i e)
    (hI : Function.Injective (fderiv ℝ (A.phaseRealChartMap i e.symm F)
      ((analyticPhaseChart A i e) p)))
    (hHess : 0 < PhaseGeometry.coordinateMetricHessian
      (RealModes.inducedCoordinateMetric (A.phaseRealChartMap i e.symm F))
      Prod.fst ((analyticPhaseChart A i e) p) SmallModes.dy SmallModes.dy) :
    ∃ data : SmoothSurfaceProfileGeometry M p,
      data.chart = analyticPhaseChart A i e ∧
      data.u = coordinateSurfaceX (F ∘ (analyticPhaseChart A i e).symm) ∧
      data.v = coordinateSurfaceY (F ∘ (analyticPhaseChart A i e).symm) ∧
      data.acc = coordinateSurfaceYY (F ∘ (analyticPhaseChart A i e).symm) := by
  have hg := analytic_phase_raw_germ_on_outer_domain A i e F hx
  obtain ⟨k,l,normal,hgauss,hk,hnu,hnv⟩ :=
    analytic_phase_gauss_certificate_of_germ A i e hi hF hg hI hHess
  let data := geometryOfCoordinateSurface hF (analyticPhaseChart A i e)
    (analytic_phase_chart_inverse_smooth A i e hi) hp
    (analytic_phase_coordinate_derivative_injective_of_germ A i e hi hF hg hI)
    normal k l hgauss hk hnu hnv
  exact ⟨data, rfl, rfl, rfl, rfl⟩

theorem analytic_raw_profiles_of_phase_profiles (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {F W : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hW : ContMDiff planeModel spaceModel ∞ W) {p : M}
    (data : SmoothSurfaceProfileGeometry M p)
    (hchart : data.chart = analyticPhaseChart A i e)
    (hu : data.u = coordinateSurfaceX (F ∘ (analyticPhaseChart A i e).symm))
    (hv : data.v = coordinateSurfaceY (F ∘ (analyticPhaseChart A i e).symm))
    (hacc : data.acc = coordinateSurfaceYY (F ∘ (analyticPhaseChart A i e).symm))
    {r ε : ℝ}
    (hweight : ∀ q ∈ Metric.ball (data.chart p) r,
      A.chartWeight i (e.symm (baseEquiv.symm q)) ≠ 0)
    (hprofiles : ∀ q ∈ Metric.ball (data.chart p) r,
      AnalyticFirstProfileEstimate (A.phaseRealChartMap i e.symm F)
        (A.phaseRealChartMap i e.symm W) q ε) :
    data.HasRawFirstProfiles r ε W := by
  intro q hq
  obtain ⟨w,hwY,hwYY,hx,hy⟩ := hprofiles q hq
  have hFX := analytic_phase_fderiv A i e hi hF (hweight q hq) (1, 0)
  have hFY := analytic_phase_fderiv A i e hi hF (hweight q hq) (0, 1)
  have hFYY := analytic_phase_yy A i e hi hF (hweight q hq)
  have hWX := analytic_phase_fderiv A i e hi hW (hweight q hq) (1, 0)
  have hWY := analytic_phase_fderiv A i e hi hW (hweight q hq) (0, 1)
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · change w ⬝ᵥ rawToSpace.symm (data.v q) = 0
    rw [hv]
    change w ⬝ᵥ rawToSpace.symm
      (fderiv ℝ (F ∘ (analyticPhaseChart A i e).symm) q (0, 1)) = 0
    rw [← hFY]
    exact hwY
  · change w ⬝ᵥ rawToSpace.symm (data.acc q) = 0
    rw [hacc, ← hFYY]
    exact hwYY
  · rw [hchart, hu]
    simp only [coordinateSurfaceX, map_sub]
    rw [← hWX, ← hFX]
    exact hx
  · rw [hchart, hv]
    simp only [coordinateSurfaceY, map_sub]
    rw [← hWY, ← hFY]
    exact hy

theorem analytic_raw_profiles_of_phase_profiles_on_outer_domain
    (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {F W : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hW : ContMDiff planeModel spaceModel ∞ W) {p : M}
    (data : SmoothSurfaceProfileGeometry M p)
    (hchart : data.chart = analyticPhaseChart A i e)
    (hu : data.u = coordinateSurfaceX (F ∘ (analyticPhaseChart A i e).symm))
    (hv : data.v = coordinateSurfaceY (F ∘ (analyticPhaseChart A i e).symm))
    (hacc : data.acc = coordinateSurfaceYY (F ∘ (analyticPhaseChart A i e).symm))
    {r ε : ℝ}
    (hdomain : ∀ q ∈ Metric.ball (data.chart p) r,
      q ∈ analyticPhaseOuterDomain A i e)
    (hprofiles : ∀ q ∈ Metric.ball (data.chart p) r,
      AnalyticFirstProfileEstimate (A.phaseRealChartMap i e.symm F)
        (A.phaseRealChartMap i e.symm W) q ε) :
    data.HasRawFirstProfiles r ε W := by
  intro q hq
  obtain ⟨w,hwY,hwYY,hx,hy⟩ := hprofiles q hq
  obtain ⟨hFfirst,hFYY⟩ := analytic_phase_first_and_yy_on_outer_domain A i e hi hF
    (hdomain q hq)
  have hWfirst := (analytic_phase_first_and_yy_on_outer_domain A i e hi hW
    (hdomain q hq)).1
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · change w ⬝ᵥ rawToSpace.symm (data.v q) = 0
    rw [hv]
    change w ⬝ᵥ rawToSpace.symm
      (fderiv ℝ (F ∘ (analyticPhaseChart A i e).symm) q (0, 1)) = 0
    rw [← hFfirst (0, 1)]
    exact hwY
  · change w ⬝ᵥ rawToSpace.symm (data.acc q) = 0
    rw [hacc, ← hFYY]
    exact hwYY
  · rw [hchart, hu]
    simp only [coordinateSurfaceX, map_sub]
    rw [← hWfirst (1, 0), ← hFfirst (1, 0)]
    exact hx
  · rw [hchart, hv]
    simp only [coordinateSurfaceY, map_sub]
    rw [← hWfirst (0, 1), ← hFfirst (0, 1)]
    exact hy

end R4Embedding
