import R4Embedding.MetricBounds
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! Connect the metric-preserving manifold derivative to the ordinary
derivative of a coordinate map. The domain has the actual product norm used
by the profile estimates; no isometry between coordinate norms is assumed. -/

noncomputable section

namespace R4Embedding

open Bundle Manifold
open scoped ContDiff

abbrev pairModel := 𝓘(ℝ, ℝ × ℝ)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

/-- Tangent derivative of a parametrization, with its normed-space source. -/
def coordinateTangentMap (c : (ℝ × ℝ) → M) (q : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] TangentSpace planeModel (c q) :=
  mfderiv pairModel planeModel c q

theorem IsSmoothIsometricMap.fderiv_comp_coordinate
    {g : SmoothMetric M} {f : M → Space} (hf : IsSmoothIsometricMap g f)
    {c : (ℝ × ℝ) → M} {q : ℝ × ℝ}
    (hc : MDifferentiableAt pairModel planeModel c q) :
    fderiv ℝ (f ∘ c) q = (euclideanDerivative f (c q)).comp (coordinateTangentMap c q) := by
  change fderiv ℝ (f ∘ c) q =
    (mvfderiv planeModel f (c q)).comp (mfderiv pairModel planeModel c q)
  rw [← mvfderiv_eq_fderiv]
  exact mvfderiv_comp q (hf.1.mdifferentiableAt (by simp)) hc

theorem IsSmoothIsometricMap.hasFDerivAt_comp_coordinate
    {g : SmoothMetric M} {f : M → Space} (hf : IsSmoothIsometricMap g f)
    {c : (ℝ × ℝ) → M} {q : ℝ × ℝ}
    (hc : MDifferentiableAt pairModel planeModel c q) :
    HasFDerivAt (f ∘ c)
      ((euclideanDerivative f (c q)).comp (coordinateTangentMap c q)) q := by
  rw [← hf.fderiv_comp_coordinate hc]
  exact ((hf.1.mdifferentiableAt (by simp)).comp q hc).differentiableAt.hasFDerivAt

/-- A bound selected from the pulled-back metric works for every isometric
output's ordinary coordinate derivative. -/
theorem exists_uniform_isometric_chart_derivative_bound
    (g : SmoothMetric M) (c : (ℝ × ℝ) → M) {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hc : ∀ q ∈ K, MDifferentiableAt pairModel planeModel c q)
    (h₀ : ContinuousOn (fun q => g.inner (c q)
      (coordinateTangentMap c q (1, 0)) (coordinateTangentMap c q (1, 0))) K)
    (h₁ : ContinuousOn (fun q => g.inner (c q)
      (coordinateTangentMap c q (0, 1)) (coordinateTangentMap c q (0, 1))) K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ f : M → Space, IsSmoothIsometricMap g f →
      ∀ q ∈ K, ‖fderiv ℝ (f ∘ c) q‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ := exists_uniform_isometric_coordinate_bound g c
    (coordinateTangentMap c) hK h₀ h₁
  refine ⟨B, hB, ?_⟩
  intro f hf q hq
  rw [hf.fderiv_comp_coordinate (hc q hq)]
  exact hbound f hf q hq

end R4Embedding
