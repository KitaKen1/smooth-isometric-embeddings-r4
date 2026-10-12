import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadBounds
import OAI.Geometry.SurfaceImmersion.Primitive.SupportedPrimitiveGeometry

/-! The exterior derivative budget uses the actual slow map G, fast map V,
and exact output W. On a neighbourhood where V=G, the W-F derivative error
is the sum of the correction W-V and slow displacement G-F. -/

noncomputable section
namespace R4Embedding

open Set Filter Manifold
open scoped ContDiff Topology
open OAI.ClosedSurfaceR4 OAI.ClosedSurfaceR4.FiniteOrderSmoothing
open OAI.ClosedSurfaceR4.JetPolynomial

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

theorem analytic_plane_read_derivative_difference_bound (A : SmoothingAtlas M)
    (i : A.centers) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F W : M → OAI.ClosedSurfaceR4.Space),
      ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ W →
      ∀ C : ℝ, 0 ≤ C → A.WeightedBound 1 1 C (W-F) → ∀ x : ℝ × ℝ,
        ‖fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i W) x -
          fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ ≤ D*C := by
  obtain ⟨D₀,hD₀,hd⟩ := A.vectorPlaneRead_bound (V := OAI.ClosedSurfaceR4.Space) i 1
  let D := ‖spaceCoordinates.toContinuousLinearMap‖*D₀
  refine ⟨D,mul_nonneg (norm_nonneg _) hD₀,?_⟩
  intro F W hF hW C hC hclose x
  have hread := hd (W-F) 1 C zero_lt_one le_rfl hC (hW.sub hF) hclose
  have hraw := hread.linear uniqueDiffOn_univ zero_le_one
    (A.vectorPlaneRead_smooth i (hW.sub hF)).contDiffOn spaceCoordinates.toContinuousLinearMap
  have hh := (hraw.fderivWithin uniqueDiffOn_univ zero_lt_one).norm_le (mem_univ x)
  have he : spaceCoordinates ∘ A.vectorPlaneRead i (W-F) =
      (spaceCoordinates ∘ A.vectorPlaneRead i W) -
        (spaceCoordinates ∘ A.vectorPlaneRead i F) := by
    rw [A.vectorPlaneRead_sub]
    funext y
    exact map_sub spaceCoordinates _ _
  change ‖fderivWithin ℝ (spaceCoordinates ∘ A.vectorPlaneRead i (W-F)) univ x‖ ≤ _ at hh
  rw [he, fderivWithin_univ,
    fderiv_sub ((spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hW)).differentiable
      (by simp) x)
      ((spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)).differentiable
        (by simp) x)] at hh
  simpa only [div_one, D, mul_assoc] using hh

theorem analytic_exterior_coordinate_derivative_bound_in_atlas {F : M → OAI.ClosedSurfaceR4.Space}
    (A : SmoothingAtlas M)
    (houter : ∀ i x, x ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hF : ContMDiff planeModel spaceModel ∞ F) (j : A.centers) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G V W : M → OAI.ClosedSurfaceR4.Space),
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ContMDiff planeModel spaceModel ∞ W → ∀ a c : ℝ, 0 ≤ a → 0 ≤ c →
      A.WeightedBound 1 3 a (G-F) → A.WeightedBound 1 2 c (W-V) →
      ∀ p : M, p ∈ tsupport (A.weight j) → V =ᶠ[𝓝 p] G →
        ‖fderiv ℝ (coordinateMap W (j : M))
            (planeCoordinateIsometry (chart (j : M) p)) -
          fderiv ℝ (coordinateMap F (j : M))
            (planeCoordinateIsometry (chart (j : M) p))‖ ≤ D*(a+c) := by
  obtain ⟨D,hD,hd⟩ := analytic_plane_read_derivative_difference_bound A j
  refine ⟨D,hD,?_⟩
  intro G V W hG hV hW a c ha hc hslow hcorrection p hp hVG
  let x := planeCoordinateIsometry (chart (j : M) p)
  have hread (H : M → OAI.ClosedSurfaceR4.Space) :
      fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead j H) x =
        fderiv ℝ (coordinateMap H (j : M)) x :=
    (A.vectorPlaneRead_eventually_coordinateMap H j (houter j) hp)
      |>.fderiv_eq (𝕜 := ℝ)
  have hfirst := hd V W hV hW c hc (fun i => (hcorrection i).mono_order (by decide)) x
  have hsecond := hd F G hF hG a ha (fun i => (hslow i).mono_order (by decide)) x
  rw [hread W, hread V] at hfirst
  rw [hread G, hread F] at hsecond
  have heq : fderiv ℝ (coordinateMap V (j : M)) x =
      fderiv ℝ (coordinateMap G (j : M)) x := by
    have he := (coordinateMap_eventuallyEq_at hVG (j : M)
      (by simpa only [coordinateChart_source, chart_source] using A.weight_support j hp))
      |>.fderiv_eq (𝕜 := ℝ)
    have hpoint : coordinateChart (j : M) p = x := by
      dsimp only [x]
      rw [planeCoordinateIsometry_chart]
      rfl
    rw [hpoint] at he
    exact he
  calc
    _ = ‖(fderiv ℝ (coordinateMap W (j : M)) x -
        fderiv ℝ (coordinateMap V (j : M)) x) +
      (fderiv ℝ (coordinateMap G (j : M)) x -
        fderiv ℝ (coordinateMap F (j : M)) x)‖ := by rw [heq]; congr 1; abel
    _ ≤ ‖fderiv ℝ (coordinateMap W (j : M)) x -
        fderiv ℝ (coordinateMap V (j : M)) x‖ +
      ‖fderiv ℝ (coordinateMap G (j : M)) x -
        fderiv ℝ (coordinateMap F (j : M)) x‖ := norm_add_le _ _
    _ ≤ D*c + D*a := add_le_add hfirst hsecond
    _ = D*(a+c) := by ring

theorem analytic_exterior_coordinate_derivative_bound {g : SmoothMetric M} {F : M → OAI.ClosedSurfaceR4.Space}
    (data : MetricGoodPhaseData g F) (hF : ContMDiff planeModel spaceModel ∞ F)
    (j : data.A.centers) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G V W : M → OAI.ClosedSurfaceR4.Space),
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ContMDiff planeModel spaceModel ∞ W → ∀ a c : ℝ, 0 ≤ a → 0 ≤ c →
      data.A.WeightedBound 1 3 a (G-F) → data.A.WeightedBound 1 2 c (W-V) →
      ∀ p : M, p ∈ tsupport (data.A.weight j) → V =ᶠ[𝓝 p] G →
        ‖fderiv ℝ (coordinateMap W (j : M))
            (planeCoordinateIsometry (chart (j : M) p)) -
          fderiv ℝ (coordinateMap F (j : M))
            (planeCoordinateIsometry (chart (j : M) p))‖ ≤ D*(a+c) :=
  analytic_exterior_coordinate_derivative_bound_in_atlas data.A data.outer_locally_one hF j

end R4Embedding
