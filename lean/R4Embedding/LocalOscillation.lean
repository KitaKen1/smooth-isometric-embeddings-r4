import R4Embedding.ProjectedDerivative

/-! Continuity of the old derivative and of the transverse projection supplies
a fixed coordinate ball. The radius and residual tolerance are chosen before
the oscillating map. No bound on its second derivative is required. -/

namespace R4Embedding

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Positive tolerances can absorb a prescribed nonnegative multiplier. -/
theorem exists_positive_scaled_tolerance {q a : ℝ} (hq : 0 ≤ q) (ha : 0 < a) :
    ∃ η : ℝ, 0 < η ∧ q * η ≤ a := by
  refine ⟨a / (q + 1), div_pos ha (by linarith), ?_⟩
  calc
    q * (a / (q + 1)) = (a * q) / (q + 1) := by ring
    _ ≤ a := (div_le_iff₀ (by linarith : 0 < q + 1)).mpr (by nlinarith)

/-- Continuity makes both fixed-projection errors small on one convex ball. -/
theorem exists_local_projection_bounds
    (D : E → E →L[ℝ] V) (P : E → V →L[ℝ] V) (L : V →L[ℝ] E) (p : E)
    (hD : ContinuousAt D p) (hP : ContinuousAt P p)
    (hleft : L.comp (D p) = ContinuousLinearMap.id ℝ E)
    {η : ℝ} (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ Metric.ball p r,
      ‖L.comp (D q) - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4 ∧
      ‖P q - P p‖ ≤ η := by
  have hLD : ContinuousAt (fun q => L.comp (D q)) p :=
    continuousAt_const.clm_comp hD
  obtain ⟨r₁, hr₁, h₁⟩ := Metric.continuousAt_iff.mp hLD (1 / 4) (by norm_num)
  obtain ⟨r₂, hr₂, h₂⟩ := Metric.continuousAt_iff.mp hP η hη
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, ?_⟩
  intro q hq
  have hdist : dist q p < min r₁ r₂ := hq
  constructor
  · have h := h₁ (hdist.trans_le (min_le_left _ _))
    rw [dist_eq_norm, hleft] at h
    exact h.le
  · have h := h₂ (hdist.trans_le (min_le_right _ _))
    rw [dist_eq_norm] at h
    exact h.le

/-- The local transverse-oscillation theorem: radius and residual tolerance
are independent of the eventual oscillating map and its transverse term. -/
theorem exists_injective_ball_of_transverse_perturbation
    (D : E → E →L[ℝ] V) (P : E → V →L[ℝ] V) (L : V →L[ℝ] E) (p : E)
    (hD : ContinuousAt D p) (hP : ContinuousAt P p)
    (hleft : L.comp (D p) = ContinuousLinearMap.id ℝ E)
    (hkill : L.comp (P p) = 0) {B : ℝ} (hB : 0 ≤ B) :
    ∃ r ρ : ℝ, 0 < r ∧ 0 < ρ ∧
      ∀ (f : E → V) (df W : E → E →L[ℝ] V),
        (∀ q ∈ Metric.ball p r, HasFDerivWithinAt f (df q) (Metric.ball p r) q) →
        (∀ q ∈ Metric.ball p r, (P q).comp (W q) = W q) →
        (∀ q ∈ Metric.ball p r, ‖W q‖ ≤ B) →
        (∀ q ∈ Metric.ball p r, ‖df q - D q - W q‖ ≤ ρ) →
        Set.InjOn f (Metric.ball p r) := by
  obtain ⟨η, hη, hηbudget⟩ := exists_positive_scaled_tolerance
    (mul_nonneg (norm_nonneg L) hB) (show (0 : ℝ) < 1 / 4 by norm_num)
  obtain ⟨ρ, hρ, hρbudget⟩ := exists_positive_scaled_tolerance
    (norm_nonneg L) (show (0 : ℝ) < 1 / 4 by norm_num)
  obtain ⟨r, hr, hbounds⟩ := exists_local_projection_bounds D P L p hD hP hleft hη
  refine ⟨r, ρ, hr, hρ, ?_⟩
  intro f df W hf hrange hW hresidual
  apply injOn_of_projected_derivative_decomposition
    (old := D) (transverse := W) (residual := fun q => df q - D q - W q)
    L (a := 1 / 4) (b := 1 / 4) (c := 1 / 4) (convex_ball p r) hf
  · intro q _
    abel
  · intro q hq
    exact (hbounds q hq).1
  · intro q hq
    have h := projected_transverse_bound_of_bounds L (P q) (P p) (W q)
      (hrange q hq) hkill (hbounds q hq).2 (hW q hq)
    exact h.trans (by nlinarith [hηbudget])
  · intro q hq
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (hresidual q hq) (norm_nonneg L))).trans hρbudget
  · norm_num

end R4Embedding
