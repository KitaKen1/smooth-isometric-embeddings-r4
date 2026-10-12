import R4Analytic.AnalyticAtlasReadBounds
import R4Analytic.AnalyticAtlasC0Bounds
import R4Embedding.EmbeddingStability

/-! Weighted C-one stability using only the actual smoothing atlas and
the already checked local embedding argument. No phase preparation or
metric correction is imported. The initial embedding is an input. -/

noncomputable section
namespace R4Embedding

open Set Filter Manifold
open scoped ContDiff Topology BigOperators
open OAI.ClosedSurfaceR4 OAI.ClosedSurfaceR4.FiniteOrderSmoothing
open OAI.ClosedSurfaceR4.JetPolynomial

def analyticPairCoordinateEquiv : JetPolynomial.Base ≃L[ℝ] (ℝ × ℝ) :=
  (LinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearEquiv

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

/-- A linear change of coordinates on the supplied chart, retaining its
source and smooth structure. -/
def analyticPairChart (p : M) : OpenPartialHomeomorph M (ℝ × ℝ) :=
  (chart p).trans analyticPairCoordinateEquiv.toHomeomorph.toOpenPartialHomeomorph

theorem analytic_pair_chart_source (p : M) :
    (analyticPairChart p).source = (chart p).source := by
  simp [analyticPairChart]

theorem analytic_pair_chart_smooth (p : M) :
    ContMDiffOn planeModel pairModel ∞ (analyticPairChart p) (analyticPairChart p).source := by
  rw [analytic_pair_chart_source]
  exact analyticPairCoordinateEquiv.contDiff.contMDiff.comp_contMDiffOn (chart_smooth p)

theorem analytic_pair_chart_symm_smooth (p : M) :
    ContMDiffOn pairModel planeModel ∞ (analyticPairChart p).symm
      (analyticPairChart p).target := by
  have h := (chart_symm_smooth p).comp
    analyticPairCoordinateEquiv.symm.contDiff.contMDiff.contMDiffOn
    (fun x (hx : x ∈ (analyticPairChart p).target) => by
      simpa [analyticPairChart] using hx)
  simpa [analyticPairChart] using h

theorem analytic_chart_derivative_injective {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p))
    (e : OpenPartialHomeomorph M (ℝ × ℝ))
    (he : ContMDiffOn planeModel pairModel ∞ e e.source)
    (hi : ContMDiffOn pairModel planeModel ∞ e.symm e.target)
    {q : ℝ × ℝ} (hq : q ∈ e.target) :
    Function.Injective (fderiv ℝ (F ∘ e.symm) q) := by
  have hd : e.MDifferentiable planeModel pairModel :=
    ⟨he.mdifferentiableOn (by simp), hi.mdifferentiableOn (by simp)⟩
  have hcomp := mfderiv_comp q
    ((hF (e.symm q)).mdifferentiableAt (by simp)) (hd.mdifferentiableAt_symm hq)
  rw [mfderiv_eq_fderiv] at hcomp
  rw [hcomp]
  exact (hImm _).comp (hd.symm.mfderiv_injective hq)

def analyticPairActiveDomain (A : SmoothingAtlas M) (i : A.centers) : Set (ℝ × ℝ) :=
  (analyticPairChart (i : M)).target ∩
    (analyticPairChart (i : M)).symm ⁻¹' {p | A.weight i p ≠ 0}

theorem analytic_pair_active_isOpen (A : SmoothingAtlas M) (i : A.centers) :
    IsOpen (analyticPairActiveDomain A i) := by
  exact (analyticPairChart (i : M)).isOpen_inter_preimage_symm
    (isOpen_ne.preimage (A.weight_smooth i).continuous)

theorem analytic_pair_active_cover (A : SmoothingAtlas M) (p : M) :
    ∃ i : A.centers, p ∈ (analyticPairChart (i : M)).source ∧
      analyticPairChart (i : M) p ∈ analyticPairActiveDomain A i := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : A.centers, A.weight i p ≠ 0 := by
    by_contra! hzero
    have h := A.partition p
    simp only [hzero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] at h
    norm_num at h
  have hs : p ∈ (analyticPairChart (i : M)).source := by
    rw [analytic_pair_chart_source]
    exact A.weight_support i (subset_tsupport (A.weight i) hi)
  refine ⟨i, hs, (analyticPairChart (i : M)).map_source hs, ?_⟩
  change A.weight i ((analyticPairChart (i : M)).symm (analyticPairChart (i : M) p)) ≠ 0
  rwa [(analyticPairChart (i : M)).left_inv hs]

variable [CompactSpace M]

theorem analytic_weighted_pair_derivative_difference_bound (A : SmoothingAtlas M)
    (i : A.centers) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F W : M → Space),
      ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ W →
      ∀ C : ℝ, 0 ≤ C → A.WeightedBound 1 1 C (W - F) →
      ∀ q : ℝ × ℝ, q ∈ analyticPairActiveDomain A i →
        ‖fderiv ℝ (W ∘ (analyticPairChart (i : M)).symm) q -
          fderiv ℝ (F ∘ (analyticPairChart (i : M)).symm) q‖ ≤ D * C := by
  obtain ⟨D, hD, hd⟩ := analytic_weighted_chart_derivative_difference_bound (V := Space) A i
  refine ⟨D * ‖analyticPairCoordinateEquiv.symm.toContinuousLinearMap‖,
    mul_nonneg hD (norm_nonneg _), ?_⟩
  intro F W hF hW C hC hclose q hq
  let x := analyticPairCoordinateEquiv.symm q
  have hx : x ∈ (chart (i : M)).target := by
    simpa [analyticPairChart, x] using hq.1
  have hw : A.weight i ((chart (i : M)).symm x) ≠ 0 := hq.2
  have he (H : M → Space) (hH : ContMDiff planeModel spaceModel ∞ H) :
      fderiv ℝ (H ∘ (analyticPairChart (i : M)).symm) q =
        (fderiv ℝ (H ∘ (chart (i : M)).symm) x).comp
          analyticPairCoordinateEquiv.symm.toContinuousLinearMap := by
    have hh := ((hH.comp_contMDiffOn (chart_symm_smooth (i : M))).contDiffOn x hx).contDiffAt
      ((chart (i : M)).open_target.mem_nhds hx)
    change fderiv ℝ ((H ∘ (chart (i : M)).symm) ∘ analyticPairCoordinateEquiv.symm) q = _
    rw [fderiv_comp q (hh.differentiableAt (by simp))
      analyticPairCoordinateEquiv.symm.differentiableAt, analyticPairCoordinateEquiv.symm.fderiv]
  rw [he W hW, he F hF, ← ContinuousLinearMap.sub_comp]
  have hb := hd F W hF hW C hC hclose x hx hw
  calc
    _ ≤ ‖fderiv ℝ (W ∘ (chart (i : M)).symm) x -
        fderiv ℝ (F ∘ (chart (i : M)).symm) x‖ *
          ‖analyticPairCoordinateEquiv.symm.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (D * C) * ‖analyticPairCoordinateEquiv.symm.toContinuousLinearMap‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = _ := by ring

/-- A single positive tolerance, fixed before every future map, preserves
the given embedding using the actual weighted atlas C-one error. -/
theorem analytic_initial_weighted_embedding_tolerance (A : SmoothingAtlas M)
    {F : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (hFinj : Function.Injective F)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ W : M → Space,
      ContMDiff planeModel spaceModel ∞ W →
      A.WeightedBound 1 1 ε (W - F) → Topology.IsClosedEmbedding W := by
  classical
  choose index hsource hdomain using analytic_pair_active_cover A
  let data := fun p => geometryOfCoordinateImmersion hF (analyticPairChart (index p : M))
    (analytic_pair_chart_symm_smooth (index p : M)) (hsource p)
    (analytic_chart_derivative_injective hF hImm (analyticPairChart (index p : M))
      (analytic_pair_chart_smooth (index p : M)) (analytic_pair_chart_symm_smooth (index p : M))
      ((analyticPairChart (index p : M)).map_source (hsource p)))
  let U := fun p => analyticPairActiveDomain A (index p)
  obtain ⟨centers, r, δ, η, hδ, hη, hr, _hcover, hstable⟩ :=
    exists_closed_embedding_tolerance_of_derivative_close_in_open hF hFinj data
      (fun _ => rfl) (fun _ => rfl) U (fun p => analytic_pair_active_isOpen A (index p)) hdomain
  choose D hD hd using analytic_weighted_pair_derivative_difference_bound A
  let total := (∑ p ∈ centers, D (index p)) + 1
  have htotal : 0 < total := by
    have hs : 0 ≤ ∑ p ∈ centers, D (index p) := Finset.sum_nonneg (fun p _ => hD (index p))
    dsimp [total]
    linarith
  let count : ℝ := Fintype.card A.centers
  have hcount : 0 ≤ count := by dsimp [count]; positivity
  let ε := min (δ / total) (η / (2 * (count + 1)))
  have hε : 0 < ε := lt_min (div_pos hδ htotal) (div_pos hη (by positivity))
  have hfirst : total * ε ≤ δ := by
    have hh : ε * total ≤ δ := (le_div_iff₀ htotal).mp (min_le_left _ _)
    nlinarith
  have hzero : 2 * (count + 1) * ε ≤ η := by
    have hh : ε * (2 * (count + 1)) ≤ η :=
      (le_div_iff₀ (by positivity : 0 < 2 * (count + 1))).mp (min_le_right _ _)
    nlinarith
  refine ⟨ε, hε, ?_⟩
  intro W hW hclose
  apply hstable W hW
  · intro p hp q hq
    have hqU : q ∈ U p := ((hr p).2 (Metric.ball_subset_closedBall hq)).2
    have hsmall : D (index p) ≤ total := by
      have hh := Finset.single_le_sum (fun a _ => hD (index a)) hp
      dsimp [total]
      linarith
    have hh := hd (index p) F W hF hW ε hε.le hclose q hqU
    change ‖fderiv ℝ (W ∘ (analyticPairChart (index p : M)).symm) q -
      fderiv ℝ (F ∘ (analyticPairChart (index p : M)).symm) q‖ ≤ δ
    exact hh.trans (by nlinarith)
  · intro p
    have hh := analytic_atlas_dist_le A hε.le hclose p
    change dist (W p) (F p) ≤ count * ε at hh
    exact hh.trans_lt (by nlinarith)

end R4Embedding
