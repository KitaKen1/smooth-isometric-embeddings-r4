import R4Analytic.AnalyticProfileTransfer
import R4Embedding.CoordinateSurfaceGeometry
import OAI.Geometry.SurfaceImmersion.Primitive.PhaseBoundaryProfile

/-! On the active weight locus, the globally localized phase map agrees
as a germ with the genuine surface chart. In particular its first derivatives
are the actual coordinate derivatives, with no extra assumed identification. -/

noncomputable section
namespace R4Embedding

open Set Filter Manifold
open scoped ContDiff Topology
open OAI.ClosedSurfaceR4 OAI.ClosedSurfaceR4.FiniteOrderSmoothing
open OAI.ClosedSurfaceR4.SurfaceJetCoordinates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

def analyticPhaseChart (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) :
    OpenPartialHomeomorph M (ℝ × ℝ) :=
  ((OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chart (i : M)).trans e).trans
    baseEquiv.toHomeomorph.toOpenPartialHomeomorph

theorem analyticPhaseChart_symm (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (x : ℝ × ℝ) :
    (analyticPhaseChart A i e).symm x =
      (OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chart (i : M)).symm
        (e.symm (baseEquiv.symm x)) := rfl

theorem analytic_phase_raw_germ (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) (F : M → Space) {x : ℝ × ℝ}
    (hx : A.chartWeight i (e.symm (baseEquiv.symm x)) ≠ 0) :
    A.phaseRealChartMap i e.symm F =ᶠ[𝓝 x]
      rawToSpace.symm ∘ F ∘ (analyticPhaseChart A i e).symm := by
  have hc : Continuous (fun y : ℝ × ℝ => A.chartWeight i (e.symm (baseEquiv.symm y))) :=
    (A.chartWeight_smooth i).continuous.comp (hi.continuous.comp baseEquiv.symm.continuous)
  filter_upwards [hc.continuousAt.eventually_ne hx] with y hy
  have hs : e.symm (baseEquiv.symm y) ∈
      (A.chartWeightCompact i : Set JetPolynomial.Base) := by
    rw [← A.chartWeight_tsupport i]
    exact subset_tsupport (A.chartWeight i) hy
  change OAI.ClosedSurfaceR4.spaceCoordinates
      (A.vectorChartRead i F (e.symm (baseEquiv.symm y))) =
    rawToSpace.symm (F ((analyticPhaseChart A i e).symm y))
  rw [A.vectorChartRead_on_support i F hs, analyticPhaseChart_symm]
  rfl

theorem analytic_phase_coordinate_contDiffAt (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {x : ℝ × ℝ}
    (hx : A.chartWeight i (e.symm (baseEquiv.symm x)) ≠ 0) :
    ContDiffAt ℝ ∞ (F ∘ (analyticPhaseChart A i e).symm) x := by
  have hg := analytic_phase_raw_germ A i e hi F hx
  have he : rawToSpace ∘ A.phaseRealChartMap i e.symm F =ᶠ[𝓝 x]
      F ∘ (analyticPhaseChart A i e).symm := by
    filter_upwards [hg] with y hy
    simp only [Function.comp_apply, hy, ContinuousLinearEquiv.apply_symm_apply]
  exact ((rawToSpace.contDiff.comp (A.phaseRealChartMap_smooth i hi hF)).contDiffAt)
    |>.congr_of_eventuallyEq he.symm

theorem analytic_phase_fderiv (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {x : ℝ × ℝ}
    (hx : A.chartWeight i (e.symm (baseEquiv.symm x)) ≠ 0) (v : ℝ × ℝ) :
    fderiv ℝ (A.phaseRealChartMap i e.symm F) x v =
      rawToSpace.symm (fderiv ℝ (F ∘ (analyticPhaseChart A i e).symm) x v) := by
  have hg := analytic_phase_raw_germ A i e hi F hx
  have hcoord := (analytic_phase_coordinate_contDiffAt A i e hi hF hx)
    |>.differentiableAt (by simp)
  have hchain := (rawToSpace.symm.hasFDerivAt.comp x hcoord.hasFDerivAt).fderiv
  have hsame := hg.fderiv_eq (𝕜 := ℝ)
  rw [hchain] at hsame
  exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] RawVector => L v) hsame

theorem analytic_phase_fderiv_germ (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {x : ℝ × ℝ}
    (hx : A.chartWeight i (e.symm (baseEquiv.symm x)) ≠ 0) (v : ℝ × ℝ) :
    (fun q => fderiv ℝ (A.phaseRealChartMap i e.symm F) q v) =ᶠ[𝓝 x]
      rawToSpace.symm ∘ (fun q => fderiv ℝ (F ∘ (analyticPhaseChart A i e).symm) q v) := by
  have hc : Continuous (fun y : ℝ × ℝ => A.chartWeight i (e.symm (baseEquiv.symm y))) :=
    (A.chartWeight_smooth i).continuous.comp (hi.continuous.comp baseEquiv.symm.continuous)
  filter_upwards [hc.continuousAt.eventually_ne hx] with y hy
  exact analytic_phase_fderiv A i e hi hF hy v

theorem analytic_phase_yy (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {x : ℝ × ℝ}
    (hx : A.chartWeight i (e.symm (baseEquiv.symm x)) ≠ 0) :
    fderiv ℝ (fun q => fderiv ℝ (A.phaseRealChartMap i e.symm F) q (0, 1)) x (0, 1) =
      rawToSpace.symm (coordinateSurfaceYY (F ∘ (analyticPhaseChart A i e).symm) x) := by
  have hg := analytic_phase_fderiv_germ A i e hi hF hx (0, 1)
  have hY := (coordinateSurfaceY_contDiffAt
    (analytic_phase_coordinate_contDiffAt A i e hi hF hx)).differentiableAt (by simp)
  have hchain := (rawToSpace.symm.hasFDerivAt.comp x hY.hasFDerivAt).fderiv
  have hsame := hg.fderiv_eq (𝕜 := ℝ)
  -- `coordinateSurfaceY` is the derivative in the second coordinate by definition; fold it so
  -- that the chain rule applies syntactically.
  change _ = fderiv ℝ (rawToSpace.symm ∘ coordinateSurfaceY (F ∘ (analyticPhaseChart A i e).symm))
    x at hsame
  rw [hchain] at hsame
  exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] RawVector => L (0, 1)) hsame

end R4Embedding
