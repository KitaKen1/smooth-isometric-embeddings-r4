import R4Analytic.AnalyticPhaseCoordinates
import R4Embedding.CoordinateGerms
import R4Embedding.CoordinateRegions

/-! Locally constant outer cutoffs identify the true coordinate germ even
at the boundary of the closed weight support. No nonzero inner weight is
assumed in these transfers. Preparation and injectivity remain separate.
-/

noncomputable section
namespace R4Embedding

open Set Filter Manifold
open scoped ContDiff Topology
open OAI.ClosedSurfaceR4 OAI.ClosedSurfaceR4.FiniteOrderSmoothing
open OAI.ClosedSurfaceR4.SurfaceJetCoordinates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

def analyticPhaseOuterDomain (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) : Set (ℝ × ℝ) :=
  chartConstantRegion (analyticPhaseChart A i e) (A.outer i) 1

theorem analytic_phase_outer_domain_isOpen (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) :
    IsOpen (analyticPhaseOuterDomain A i e) :=
  chartConstantRegion_isOpen _ _ _

theorem analytic_phase_raw_germ_of_outer_one (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (F : M → Space)
    {x : ℝ × ℝ} (hx : x ∈ (analyticPhaseChart A i e).target)
    (houter : A.outer i =ᶠ[𝓝 ((analyticPhaseChart A i e).symm x)] (fun _ => 1)) :
    A.phaseRealChartMap i e.symm F =ᶠ[𝓝 x]
      rawToSpace.symm ∘ F ∘ (analyticPhaseChart A i e).symm := by
  have ho : ∀ᶠ y in 𝓝 x, A.outer i ((analyticPhaseChart A i e).symm y) = 1 :=
    houter.comp_tendsto ((analyticPhaseChart A i e).continuousAt_symm hx).tendsto
  filter_upwards [(analyticPhaseChart A i e).open_target.mem_nhds hx, ho] with y hy hone
  change spaceCoordinates
      (localize (i : M) (A.outer i) F (e.symm (baseEquiv.symm y))) =
    rawToSpace.symm (F ((analyticPhaseChart A i e).symm y))
  -- `hy.2.2` is a membership in a preimage; state it at the point of the goal so that the
  -- indicator rewrites syntactically.
  rw [localize, indicator_of_mem
    (show e.symm (baseEquiv.symm y) ∈ (chart (i : M)).target from hy.2.2)]
  change spaceCoordinates
      ((A.outer i ((analyticPhaseChart A i e).symm y))^2 •
        F ((analyticPhaseChart A i e).symm y)) = _
  rw [hone, one_pow, one_smul]
  rfl

theorem analytic_phase_raw_germ_on_closed_weight (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (F : M → Space)
    (houter : ∀ p ∈ tsupport (A.weight i), A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {x : ℝ × ℝ} (hx : x ∈ (analyticPhaseChart A i e).target)
    (hweight : e.symm (baseEquiv.symm x) ∈
      (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    A.phaseRealChartMap i e.symm F =ᶠ[𝓝 x]
      rawToSpace.symm ∘ F ∘ (analyticPhaseChart A i e).symm := by
  obtain ⟨p,hp,hpx⟩ := hweight
  have heq : (analyticPhaseChart A i e).symm x = p := by
    rw [analyticPhaseChart_symm, ← hpx, (chart (i : M)).left_inv (A.weight_support i hp)]
  apply analytic_phase_raw_germ_of_outer_one A i e F hx
  simpa only [heq] using houter p hp

theorem analytic_phase_first_and_yy_on_closed_weight (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (houter : ∀ p ∈ tsupport (A.weight i), A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {x : ℝ × ℝ} (hx : x ∈ (analyticPhaseChart A i e).target)
    (hweight : e.symm (baseEquiv.symm x) ∈
      (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    (∀ v : ℝ × ℝ, fderiv ℝ (A.phaseRealChartMap i e.symm F) x v =
      rawToSpace.symm (fderiv ℝ (F ∘ (analyticPhaseChart A i e).symm) x v)) ∧
    fderiv ℝ (fun q => fderiv ℝ (A.phaseRealChartMap i e.symm F) q (0, 1)) x (0, 1) =
      rawToSpace.symm (coordinateSurfaceYY (F ∘ (analyticPhaseChart A i e).symm) x) :=
  coordinate_first_and_yy_of_raw_germ (A.phaseRealChartMap_smooth i hi hF)
    (analytic_phase_raw_germ_on_closed_weight A i e F houter hx hweight)

theorem analytic_phase_mem_outer_domain_on_closed_weight (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (houter : ∀ p ∈ tsupport (A.weight i), A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {x : ℝ × ℝ} (hx : x ∈ (analyticPhaseChart A i e).target)
    (hweight : e.symm (baseEquiv.symm x) ∈
      (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    x ∈ analyticPhaseOuterDomain A i e := by
  obtain ⟨p,hp,hpx⟩ := hweight
  have heq : (analyticPhaseChart A i e).symm x = p := by
    rw [analyticPhaseChart_symm, ← hpx, (chart (i : M)).left_inv (A.weight_support i hp)]
  refine ⟨hx, ?_⟩
  change (analyticPhaseChart A i e).symm x ∈ interior {p | A.outer i p = 1}
  rw [heq]
  exact mem_interior_iff_mem_nhds.mpr (houter p hp)

theorem analytic_phase_raw_germ_on_outer_domain (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (F : M → Space)
    {x : ℝ × ℝ} (hx : x ∈ analyticPhaseOuterDomain A i e) :
    A.phaseRealChartMap i e.symm F =ᶠ[𝓝 x]
      rawToSpace.symm ∘ F ∘ (analyticPhaseChart A i e).symm :=
  analytic_phase_raw_germ_of_outer_one A i e F hx.1
    (locally_constant_of_mem_chartConstantRegion _ _ _ hx)

theorem analytic_phase_first_and_yy_on_outer_domain (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    {x : ℝ × ℝ} (hx : x ∈ analyticPhaseOuterDomain A i e) :
    (∀ v : ℝ × ℝ, fderiv ℝ (A.phaseRealChartMap i e.symm F) x v =
      rawToSpace.symm (fderiv ℝ (F ∘ (analyticPhaseChart A i e).symm) x v)) ∧
    fderiv ℝ (fun q => fderiv ℝ (A.phaseRealChartMap i e.symm F) q (0, 1)) x (0, 1) =
      rawToSpace.symm (coordinateSurfaceYY (F ∘ (analyticPhaseChart A i e).symm) x) :=
  coordinate_first_and_yy_of_raw_germ (A.phaseRealChartMap_smooth i hi hF)
    (analytic_phase_raw_germ_on_outer_domain A i e F hx)

end R4Embedding
