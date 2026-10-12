import OAI.Geometry.SurfaceImmersion.Atlas.AtlasWeightedBounds

/-! The actual square partition converts localized zero-order bounds into
global position bounds. No differentiability or phase choice is needed. -/

noncomputable section
namespace R4Embedding

open Set Manifold
open scoped ContDiff BigOperators
open OAI.ClosedSurfaceR4 OAI.ClosedSurfaceR4.FiniteOrderSmoothing

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem analytic_atlas_norm_le (A : SmoothingAtlas M) {t C : ℝ} {m : ℕ}
    {f : M → V} (hC : 0 ≤ C) (hb : A.WeightedBound t m C f) (p : M) :
    ‖f p‖ ≤ (Fintype.card A.centers : ℝ) * C := by
  classical
  have hlocal (i : A.centers) : ‖(A.weight i p)^2 • f p‖ ≤ C := by
    by_cases hi : A.weight i p = 0
    · simpa only [hi, zero_pow (by decide : 2 ≠ 0), zero_smul, norm_zero] using hC
    · have hp := A.weight_support i (subset_tsupport (A.weight i) hi)
      have h := (hb i).norm_le (mem_univ (chart (i : M) p))
      rwa [localize_chart (i : M) (A.weight i) f hp] at h
  calc
    ‖f p‖ = ‖∑ i : A.centers, (A.weight i p)^2 • f p‖ := by
      rw [← Finset.sum_smul, A.partition p, one_smul]
    _ ≤ ∑ i : A.centers, ‖(A.weight i p)^2 • f p‖ := norm_sum_le _ _
    _ ≤ ∑ _i : A.centers, C := Finset.sum_le_sum (fun i _ => hlocal i)
    _ = (Fintype.card A.centers : ℝ) * C := by simp

theorem analytic_atlas_dist_le (A : SmoothingAtlas M) {t C : ℝ} {m : ℕ}
    {F W : M → V} (hC : 0 ≤ C) (hb : A.WeightedBound t m C (W - F)) (p : M) :
    dist (W p) (F p) ≤ (Fintype.card A.centers : ℝ) * C := by
  simpa only [dist_eq_norm, Pi.sub_apply] using analytic_atlas_norm_le A hC hb p

theorem analytic_same_output_dist_le (A : SmoothingAtlas M)
    {F G V₀ W : M → V} {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hslow : A.WeightedBound 1 3 a (G - F))
    (hfast : A.WeightedBound 1 0 b (V₀ - G))
    (hcorrection : A.WeightedBound 1 2 c (W - V₀)) (p : M) :
    dist (W p) (F p) ≤ (Fintype.card A.centers : ℝ) * (a + b + c) := by
  have hs := analytic_atlas_dist_le A ha hslow p
  have hf := analytic_atlas_dist_le A hb hfast p
  have he := analytic_atlas_dist_le A hc hcorrection p
  calc
    dist (W p) (F p) ≤ dist (W p) (V₀ p) + dist (V₀ p) (F p) := dist_triangle _ _ _
    _ ≤ dist (W p) (V₀ p) + (dist (V₀ p) (G p) + dist (G p) (F p)) :=
      add_le_add_right (dist_triangle _ _ _) _
    _ ≤ _ := by nlinarith

end R4Embedding
