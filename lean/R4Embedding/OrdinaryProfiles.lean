import R4Embedding.CoordinateSurfaceGeometry

/-! Outside the region of oscillation, ordinary C-one closeness suffices.
The auxiliary testing field is the old x derivative itself, so no Hessian
or curvature condition is required there. All fields still use the actual F.
-/

noncomputable section
namespace R4Embedding

open Bundle Manifold
open scoped ContDiff

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

/-- A chart for ordinary derivative closeness. The testing field `acc` is
auxiliary and is not claimed to be the second derivative of F. -/
def geometryOfCoordinateImmersion {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (e : OpenPartialHomeomorph M (ℝ × ℝ))
    (he : ContMDiffOn pairModel planeModel ∞ e.symm e.target)
    {p : M} (hp : p ∈ e.source)
    (hinj : Function.Injective (fderiv ℝ (F ∘ e.symm) (e p))) :
    SmoothSurfaceProfileGeometry M p where
  toSurfaceProfileGeometry := {
    chart := e
    mem_source := hp
    u := coordinateSurfaceX (F ∘ e.symm)
    v := coordinateSurfaceY (F ∘ e.symm)
    acc := coordinateSurfaceX (F ∘ e.symm)
    u_continuous := (coordinateSurfaceX_contDiffAt
      (coordinate_surface_contDiffAt hF e he hp)).continuousAt
    v_continuous := (coordinateSurfaceY_contDiffAt
      (coordinate_surface_contDiffAt hF e he hp)).continuousAt
    acc_continuous := (coordinateSurfaceX_contDiffAt
      (coordinate_surface_contDiffAt hF e he hp)).continuousAt
    tangent_injective := by
      change Function.Injective (surfaceTangentMap
        (fderiv ℝ (F ∘ e.symm) (e p) (1, 0))
        (fderiv ℝ (F ∘ e.symm) (e p) (0, 1)))
      rw [surfaceTangentMap_of_coordinate_derivative]
      exact hinj
    normal := 0
    k := 1
    l := 0
    gauss := by simp
    k_ne_zero := one_ne_zero
    normal_u := by simp
    normal_v := by simp }
  smooth_inverse := he

/-- Pointwise ordinary C-one control supplies the same profile interface
as the active oscillating charts, with transverse vector zero. -/
theorem coordinate_first_profiles_of_derivative_close {F W : M → Space} {p : M}
    (data : SmoothSurfaceProfileGeometry M p)
    (hu : data.u = coordinateSurfaceX (F ∘ data.chart.symm))
    (hv : data.v = coordinateSurfaceY (F ∘ data.chart.symm)) {r ε : ℝ}
    (hclose : ∀ q ∈ Metric.ball (data.chart p) r,
      ‖fderiv ℝ (W ∘ data.chart.symm) q -
        fderiv ℝ (F ∘ data.chart.symm) q‖ ≤ ε) :
    data.HasFirstProfiles r ε W := by
  intro q hq
  let T := fderiv ℝ (W ∘ data.chart.symm) q -
    fderiv ℝ (F ∘ data.chart.symm) q
  have hx : ‖T (1, 0)‖ ≤ ε := by
    simpa using (T.le_opNorm (1, 0)).trans
      (mul_le_mul_of_nonneg_right (hclose q hq) (norm_nonneg (1, 0)))
  have hy : ‖T (0, 1)‖ ≤ ε := by
    simpa using (T.le_opNorm (0, 1)).trans
      (mul_le_mul_of_nonneg_right (hclose q hq) (norm_nonneg (0, 1)))
  refine ⟨0, by simp, by simp, ?_, ?_⟩
  · simpa only [hu, coordinateSurfaceX, sub_zero, sub_apply, T] using hx
  · simpa only [hv, coordinateSurfaceY, sub_apply, T] using hy

theorem geometryOfCoordinateImmersion_has_profiles {F W : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (e : OpenPartialHomeomorph M (ℝ × ℝ))
    (he : ContMDiffOn pairModel planeModel ∞ e.symm e.target)
    {p : M} (hp : p ∈ e.source)
    (hinj : Function.Injective (fderiv ℝ (F ∘ e.symm) (e p))) {r ε : ℝ}
    (hclose : ∀ q ∈ Metric.ball (e p) r,
      ‖fderiv ℝ (W ∘ e.symm) q - fderiv ℝ (F ∘ e.symm) q‖ ≤ ε) :
    (geometryOfCoordinateImmersion hF e he hp hinj).HasFirstProfiles r ε W :=
  coordinate_first_profiles_of_derivative_close
    (geometryOfCoordinateImmersion hF e he hp hinj) rfl rfl hclose

end R4Embedding
