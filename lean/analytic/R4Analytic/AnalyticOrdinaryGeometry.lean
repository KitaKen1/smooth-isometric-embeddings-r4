import R4Analytic.AnalyticExteriorBounds
import R4Embedding.OrdinaryProfiles
import R4Embedding.CoordinateNorms
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasImmersionGeometry

/-! Outside the actual action support, use a native chart with a nonzero
partition weight. The same W, V and G from the primitive construction give
ordinary first profiles there. This is a concrete atlas adapter, not an
assumption that the new output is an embedding. -/

noncomputable section
namespace R4Embedding

open Set Filter Manifold
open scoped ContDiff Topology
open OAI.ClosedSurfaceR4 OAI.ClosedSurfaceR4.FiniteOrderSmoothing

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

theorem analytic_native_coordinate_map (F : M → Space) (j : M) :
    coordinateMap F j = rawToSpace.symm ∘ F ∘ (coordinateChart j).symm := by
  funext x
  change rawToSpace.symm (F (coordinateInverse j x)) =
    rawToSpace.symm (F ((coordinateChart j).symm x))
  rw [coordinateChart_symm_apply]

theorem analytic_native_coordinate_derivative {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (j : M) {x : ℝ × ℝ}
    (hx : x ∈ (coordinateChart j).target) :
    fderiv ℝ (coordinateMap F j) x = rawToSpace.symm.toContinuousLinearMap.comp
      (fderiv ℝ (F ∘ (coordinateChart j).symm) x) := by
  have hs := coordinate_surface_contDiffAt hF (coordinateChart j)
    (coordinateChart_symm_smoothOn j) ((coordinateChart j).map_target hx)
  rw [(coordinateChart j).right_inv hx] at hs
  rw [analytic_native_coordinate_map]
  exact (rawToSpace.symm.hasFDerivAt.comp x
    (hs.differentiableAt (by simp)).hasFDerivAt).fderiv

theorem analytic_native_coordinate_derivative_injective_of_immersion {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p)) (j : M) {p : M}
    (hp : p ∈ (coordinateChart j).source) :
    Function.Injective (fderiv ℝ (F ∘ (coordinateChart j).symm) (coordinateChart j p)) := by
  have hx := (coordinateChart j).map_source hp
  have hI := coordinateMap_injective_of_immersion hF hImm j
    (by simpa only [coordinateChart_target] using hx)
  intro v w hvw
  apply hI
  rw [analytic_native_coordinate_derivative hF j hx]
  change rawToSpace.symm (fderiv ℝ (F ∘ (coordinateChart j).symm) (coordinateChart j p) v) =
    rawToSpace.symm (fderiv ℝ (F ∘ (coordinateChart j).symm) (coordinateChart j p) w)
  rw [hvw]

theorem analytic_native_coordinate_derivative_injective {g : SmoothMetric M} {F : M → Space}
    (hOld : IsSmoothIsometricMap g F) (j : M) {p : M}
    (hp : p ∈ (coordinateChart j).source) :
    Function.Injective (fderiv ℝ (F ∘ (coordinateChart j).symm) (coordinateChart j p)) :=
  analytic_native_coordinate_derivative_injective_of_immersion hOld.1 hOld.mfderiv_injective j hp

def analyticOrdinaryGeometry {g : SmoothMetric M} {F : M → Space}
    (hOld : IsSmoothIsometricMap g F) (j : M) {p : M}
    (hp : p ∈ (coordinateChart j).source) : SmoothSurfaceProfileGeometry M p :=
  geometryOfCoordinateImmersion hOld.1 (coordinateChart j) (coordinateChart_symm_smoothOn j)
    hp (analytic_native_coordinate_derivative_injective hOld j hp)

def analyticExteriorDomain (A : SmoothingAtlas M) (j : A.centers)
    (B : Set M) : Set (ℝ × ℝ) :=
  (coordinateChart (j : M)).target ∩ (coordinateChart (j : M)).symm ⁻¹'
    ({p | A.weight j p ≠ 0} ∩ Bᶜ)

theorem analytic_exterior_domain_isOpen (A : SmoothingAtlas M) (j : A.centers)
    {B : Set M} (hB : IsClosed B) : IsOpen (analyticExteriorDomain A j B) := by
  have hw : IsOpen {p | A.weight j p ≠ 0} :=
    isOpen_ne_fun (A.weight_smooth j).continuous continuous_const
  exact (coordinateChart (j : M)).symm.continuousOn.isOpen_inter_preimage
    (coordinateChart (j : M)).open_target (hw.inter hB.isOpen_compl)

/-- Every exterior point has a genuine native chart whose open domain
stays outside B and inside a nonzero partition weight. -/
theorem analytic_exterior_domains_cover (A : SmoothingAtlas M) {B : Set M}
    {p : M} (hp : p ∉ B) :
    ∃ j : A.centers, p ∈ (coordinateChart (j : M)).source ∧
      coordinateChart (j : M) p ∈ analyticExteriorDomain A j B := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : A.centers, A.weight j p ≠ 0 := by
    by_contra! hzero
    have hh := A.partition p
    simp only [hzero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] at hh
    norm_num at hh
  have hs : p ∈ (coordinateChart (j : M)).source := by
    simpa only [coordinateChart_source, chart_source] using
      A.weight_support j (subset_tsupport (A.weight j) hj)
  refine ⟨j, hs, (coordinateChart (j : M)).map_source hs, ?_⟩
  change (coordinateChart (j : M)).symm (coordinateChart (j : M) p) ∈
    {p | A.weight j p ≠ 0} ∩ Bᶜ
  rw [(coordinateChart (j : M)).left_inv hs]
  exact ⟨hj, hp⟩

/-- Fixed native-chart constant and geometry precede every future output.
The only exterior hypothesis is the germ equality V=G furnished by the
primitive construction on the complement of its precise action support. -/
theorem analytic_exterior_profiles_of_atlas_bounds {g : SmoothMetric M} {F : M → Space}
    (A : SmoothingAtlas M)
    (houter : ∀ i x, x ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hOld : IsSmoothIsometricMap g F) (j : A.centers) {p : M} (hp : p ∈ (coordinateChart (j : M)).source)
    (B : Set M) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G V W : M → Space),
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ContMDiff planeModel spaceModel ∞ W → ∀ a c : ℝ, 0 ≤ a → 0 ≤ c →
      A.WeightedBound 1 3 a (G-F) → A.WeightedBound 1 2 c (W-V) →
      (∀ y ∉ B, V =ᶠ[𝓝 y] G) → ∀ r : ℝ,
      Metric.closedBall (coordinateChart (j : M) p) r ⊆
        (coordinateChart (j : M)).target ∩ analyticExteriorDomain A j B →
      (analyticOrdinaryGeometry hOld (j : M) hp).HasFirstProfiles r (2*(D*(a+c))) W := by
  obtain ⟨D, hD, hd⟩ := analytic_exterior_coordinate_derivative_bound_in_atlas A houter hOld.1 j
  refine ⟨D, hD, ?_⟩
  intro G V W hG hV hW a c ha hc hslow hcorrection hexterior r hr
  apply geometryOfCoordinateImmersion_has_profiles hOld.1 (coordinateChart (j : M))
    (coordinateChart_symm_smoothOn (j : M)) hp
    (analytic_native_coordinate_derivative_injective hOld (j : M) hp)
  intro q hq
  have hdomain := hr (Metric.ball_subset_closedBall hq)
  let y := (coordinateChart (j : M)).symm q
  have hy : y ∈ tsupport (A.weight j) :=
    subset_tsupport (A.weight j) hdomain.2.2.1
  have hpoint : JetPolynomial.planeCoordinateIsometry (chart (j : M) y) = q := by
    rw [planeCoordinateIsometry_chart]
    exact (coordinateChart (j : M)).right_inv hdomain.1
  have hraw := hd G V W hG hV hW a c ha hc hslow hcorrection y hy
    (hexterior y hdomain.2.2.2)
  rw [hpoint, analytic_native_coordinate_derivative hW (j : M) hdomain.1,
    analytic_native_coordinate_derivative hOld.1 (j : M) hdomain.1] at hraw
  apply norm_le_twice_of_raw_coordinate_read
  simpa only [ContinuousLinearMap.comp_sub] using hraw

end R4Embedding
