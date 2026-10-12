import R4Embedding.SmoothProfileAtlas
import R4Embedding.CoordinateNorms

/-! Real-coordinate profiles can feed the smooth metric atlas directly.
The raw tolerance is halved before selecting the output. Orthogonality is
dot-product orthogonality, and all Euclidean norm losses are explicit. -/

noncomputable section

namespace R4Embedding

open Bundle Manifold
open scoped ContDiff

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

def SmoothSurfaceProfileGeometry.HasRawFirstProfiles {p : M}
    (data : SmoothSurfaceProfileGeometry M p) (r ε : ℝ) (f : M → Space) : Prop :=
  ∀ q ∈ Metric.ball (data.chart p) r, ∃ w : RawVector,
    (∑ i, w i * rawToSpace.symm (data.v q) i) = 0 ∧
    (∑ i, w i * rawToSpace.symm (data.acc q) i) = 0 ∧
    ‖rawToSpace.symm (fderiv ℝ (f ∘ data.chart.symm) q (1, 0) - data.u q) - w‖ ≤ ε ∧
    ‖rawToSpace.symm (fderiv ℝ (f ∘ data.chart.symm) q (0, 1) - data.v q)‖ ≤ ε

theorem SmoothSurfaceProfileGeometry.HasRawFirstProfiles.toFirstProfiles {p : M}
    {data : SmoothSurfaceProfileGeometry M p} {r ε : ℝ} {f : M → Space}
    (hf : data.HasRawFirstProfiles r ε f) : data.HasFirstProfiles r (2 * ε) f := by
  intro q hq
  obtain ⟨w, hwv, hwacc, hx, hy⟩ := hf q hq
  refine ⟨rawToSpace w, ?_, ?_, ?_, ?_⟩
  · simpa only [ContinuousLinearEquiv.apply_symm_apply] using rawToSpace_orthogonal hwv
  · simpa only [ContinuousLinearEquiv.apply_symm_apply] using rawToSpace_orthogonal hwacc
  · have h := (norm_rawToSpace_le
        (rawToSpace.symm (fderiv ℝ (f ∘ data.chart.symm) q (1, 0) - data.u q) - w)).trans
        (mul_le_mul_of_nonneg_left hx (by norm_num : (0 : ℝ) ≤ 2))
    simpa only [map_sub, ContinuousLinearEquiv.apply_symm_apply] using h
  · have h := (norm_rawToSpace_le
        (rawToSpace.symm (fderiv ℝ (f ∘ data.chart.symm) q (0, 1) - data.v q))).trans
        (mul_le_mul_of_nonneg_left hy (by norm_num : (0 : ℝ) ≤ 2))
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using h

theorem exists_closed_embedding_tolerance_of_raw_metric_profiles [CompactSpace M]
    (g : SmoothMetric M) (data : ∀ p : M, SmoothSurfaceProfileGeometry M p)
    {F : M → Space} (hF : Continuous F) (hFinj : Function.Injective F) :
    ∃ centers : Finset M, ∃ r : M → ℝ, ∃ ε η : ℝ,
      0 < ε ∧ 0 < η ∧
      (∀ p, 0 < r p ∧ Metric.closedBall ((data p).chart p) (r p) ⊆ (data p).chart.target) ∧
      (∀ x, ∃ p ∈ centers, x ∈ chartBallPatch (data p).chart p (r p)) ∧
      ∀ f : M → Space, IsSmoothIsometricMap g f →
        (∀ p ∈ centers, (data p).HasRawFirstProfiles (r p) ε f) →
        (∀ x, dist (f x) (F x) < η) → Topology.IsClosedEmbedding f := by
  obtain ⟨centers, r, ε, η, hε, hη, hr, hcover, htol⟩ :=
    exists_closed_embedding_tolerance_of_smooth_metric_profiles g data hF hFinj
  refine ⟨centers, r, ε / 2, η, half_pos hε, hη, hr, hcover, ?_⟩
  intro f hf hprofiles hclose
  apply htol f hf _ hclose
  intro p hp
  simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
    (hprofiles p hp).toFirstProfiles

/-- All analytic conclusions still have to hold on one map. This theorem
does not prove that analytic construction or the initial embedding exists. -/
theorem exists_isometric_embedding_of_raw_profile_construction [CompactSpace M]
    (g : SmoothMetric M) (data : ∀ p : M, SmoothSurfaceProfileGeometry M p)
    {F : M → Space} (hF : Continuous F) (hFinj : Function.Injective F)
    (hconstruct : ∀ (centers : Finset M) (r : M → ℝ) (ε η : ℝ),
      0 < ε → 0 < η →
      (∀ p, 0 < r p ∧ Metric.closedBall ((data p).chart p) (r p) ⊆ (data p).chart.target) →
      (∀ x, ∃ p ∈ centers, x ∈ chartBallPatch (data p).chart p (r p)) →
      ∃ f : M → Space, IsSmoothIsometricMap g f ∧
        (∀ p ∈ centers, (data p).HasRawFirstProfiles (r p) ε f) ∧
        (∀ x, dist (f x) (F x) < η)) :
    ∃ f : M → Space, IsSmoothIsometricEmbedding g f := by
  obtain ⟨centers, r, ε, η, hε, hη, hr, hcover, htol⟩ :=
    exists_closed_embedding_tolerance_of_raw_metric_profiles g data hF hFinj
  obtain ⟨f, hf, hprofiles, hclose⟩ := hconstruct centers r ε η hε hη hr hcover
  exact ⟨f, hf, (htol f hf hprofiles hclose).injective⟩

end R4Embedding
