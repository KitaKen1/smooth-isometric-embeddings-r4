import R4Embedding.Problem
import R4Embedding.ProfileTransfer
import Mathlib.Topology.Order.Compact

/-! Two diagonal coefficients of the metric suffice to bound a coordinate
derivative. On a compact coordinate set the bound can be selected before the
exact isometric map. No general tensor operator norm is needed. -/

noncomputable section

namespace R4Embedding

section Linear

variable {V X : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem coordinate_operator_norm_bound_of_metric
    (D : (ℝ × ℝ) →L[ℝ] V) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h₀ : inner ℝ (D (1, 0)) (D (1, 0)) ≤ a ^ 2)
    (h₁ : inner ℝ (D (0, 1)) (D (0, 1)) ≤ b ^ 2) : ‖D‖ ≤ a + b := by
  rw [real_inner_self_eq_norm_sq] at h₀ h₁
  apply coordinate_operator_norm_bound D
  · nlinarith [norm_nonneg (D (1, 0))]
  · nlinarith [norm_nonneg (D (0, 1))]

variable [TopologicalSpace X]

/-- The metric coefficients, not a previously constructed map, determine M.
The compact set may be empty. -/
theorem exists_uniform_coordinate_norm_bound_of_compact_coefficients
    {K : Set X} (hK : IsCompact K) (c₀ c₁ : X → ℝ)
    (h₀ : ContinuousOn c₀ K) (h₁ : ContinuousOn c₁ K) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ D : X → (ℝ × ℝ) →L[ℝ] V,
        (∀ q ∈ K, inner ℝ (D q (1, 0)) (D q (1, 0)) = c₀ q ∧
          inner ℝ (D q (0, 1)) (D q (0, 1)) = c₁ q) →
        ∀ q ∈ K, ‖D q‖ ≤ M := by
  obtain ⟨B₀, hB₀⟩ := hK.bddAbove_image h₀
  obtain ⟨B₁, hB₁⟩ := hK.bddAbove_image h₁
  let a := max B₀ 0 + 1
  let b := max B₁ 0 + 1
  have ha : 0 ≤ a := by dsimp [a]; linarith [le_max_right B₀ 0]
  have hb : 0 ≤ b := by dsimp [b]; linarith [le_max_right B₁ 0]
  refine ⟨a + b, add_nonneg ha hb, ?_⟩
  intro D hD q hq
  apply coordinate_operator_norm_bound_of_metric (D q) ha hb
  · rw [(hD q hq).1]
    have hc := hB₀ (Set.mem_image_of_mem c₀ hq)
    dsimp [a]
    nlinarith [le_max_left B₀ 0, le_max_right B₀ 0]
  · rw [(hD q hq).2]
    have hc := hB₁ (Set.mem_image_of_mem c₁ hq)
    dsimp [b]
    nlinarith [le_max_left B₁ 0, le_max_right B₁ 0]

end Linear

open Bundle Manifold
open scoped ContDiff

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem IsSmoothIsometricMap.coordinate_norm_sq
    {g : SmoothMetric M} {f : M → Space} (hf : IsSmoothIsometricMap g f)
    (p : M) (C : (ℝ × ℝ) →L[ℝ] TangentSpace planeModel p) (v : ℝ × ℝ) :
    ‖((euclideanDerivative f p).comp C) v‖ ^ 2 = g.inner p (C v) (C v) := by
  change ‖euclideanDerivative f p (C v)‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq, hf.2 p (C v) (C v)]

theorem IsSmoothIsometricMap.coordinate_operator_norm_bound
    {g : SmoothMetric M} {f : M → Space} (hf : IsSmoothIsometricMap g f)
    (p : M) (C : (ℝ × ℝ) →L[ℝ] TangentSpace planeModel p)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h₀ : g.inner p (C (1, 0)) (C (1, 0)) ≤ a ^ 2)
    (h₁ : g.inner p (C (0, 1)) (C (0, 1)) ≤ b ^ 2) :
    ‖(euclideanDerivative f p).comp C‖ ≤ a + b := by
  apply coordinate_operator_norm_bound_of_metric _ ha hb
  · simpa only [real_inner_self_eq_norm_sq, hf.coordinate_norm_sq p C] using h₀
  · simpa only [real_inner_self_eq_norm_sq, hf.coordinate_norm_sq p C] using h₁

/-- Uniformity holds for every exact output for the same metric, without
continuity assumptions on the family of output maps. Continuity of the two
pulled-back metric coefficients is an explicit geometric input. -/
theorem exists_uniform_isometric_coordinate_bound
    {X : Type*} [TopologicalSpace X] (g : SmoothMetric M)
    (p : X → M) (C : ∀ q, (ℝ × ℝ) →L[ℝ] TangentSpace planeModel (p q))
    {K : Set X} (hK : IsCompact K)
    (h₀ : ContinuousOn (fun q => g.inner (p q) (C q (1, 0)) (C q (1, 0))) K)
    (h₁ : ContinuousOn (fun q => g.inner (p q) (C q (0, 1)) (C q (0, 1))) K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ f : M → Space, IsSmoothIsometricMap g f →
      ∀ q ∈ K, ‖(euclideanDerivative f (p q)).comp (C q)‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ := exists_uniform_coordinate_norm_bound_of_compact_coefficients
    (V := Space) hK _ _ h₀ h₁
  refine ⟨B, hB, ?_⟩
  intro f hf
  apply hbound (fun q => (euclideanDerivative f (p q)).comp (C q))
  intro q _
  exact ⟨hf.2 (p q) (C q (1, 0)) (C q (1, 0)),
    hf.2 (p q) (C q (0, 1)) (C q (0, 1))⟩

end R4Embedding
