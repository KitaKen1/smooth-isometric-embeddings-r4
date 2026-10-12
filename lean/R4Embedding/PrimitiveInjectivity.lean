import R4Embedding.TestingProjection
import R4Embedding.ProfileTransfer

/-! Only the first two profiles of the exact output map are needed for
injectivity. A transverse velocity can be chosen independently at each point;
no smooth phase selection is needed. Metric bounds on the exact derivative
then give the uniform bound required by the local oscillation theorem. -/

noncomputable section

namespace R4Embedding

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def coordinateTransverseMap (w : V) : (ℝ × ℝ) →L[ℝ] V :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight w

theorem coordinateTransverseMap_killed (A : V →L[ℝ] (ℝ × ℝ)) {w : V} (hw : A w = 0) :
    A.comp (coordinateTransverseMap w) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  change A (x.1 • w) = 0
  rw [map_smul, hw, smul_zero]

/-- A longitudinal transverse velocity and an unchanged transverse derivative
give the required operator-norm residual. -/
theorem residual_bound_of_two_coordinate_profiles
    (df old : (ℝ × ℝ) →L[ℝ] V) (w : V) {ε : ℝ}
    (hx : ‖df (1, 0) - old (1, 0) - w‖ ≤ ε)
    (hy : ‖df (0, 1) - old (0, 1)‖ ≤ ε) :
    ‖df - old - coordinateTransverseMap w‖ ≤ 2 * ε := by
  apply (coordinate_operator_norm_bound (df - old - coordinateTransverseMap w)
    (a := ε) (b := ε) _ _).trans_eq (by ring)
  · change ‖df (1, 0) - old (1, 0) - (1 : ℝ) • w‖ ≤ ε
    simpa only [one_smul] using hx
  · change ‖df (0, 1) - old (0, 1) - (0 : ℝ) • w‖ ≤ ε
    simpa only [zero_smul, sub_zero] using hy

/-- Same-map correction, if one starts from approximate profiles instead. -/
theorem residual_bound_of_corrected_coordinate_profiles
    (df approximate old : (ℝ × ℝ) →L[ℝ] V) (w : V) {ε δ : ℝ}
    (hx : ‖approximate (1, 0) - old (1, 0) - w‖ ≤ ε)
    (hy : ‖approximate (0, 1) - old (0, 1)‖ ≤ ε)
    (hc : ‖df - approximate‖ ≤ δ) :
    ‖df - old - coordinateTransverseMap w‖ ≤ 2 * ε + δ :=
  corrected_derivative_residual_bound df approximate old (coordinateTransverseMap w)
    (residual_bound_of_two_coordinate_profiles approximate old w hx hy) hc

/-- Pointwise existential profiles suffice: the chosen velocity need not be
continuous. Tolerances are fixed before choosing the exact output map. -/
theorem exists_injective_ball_of_pointwise_profiles
    (D : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] V)
    (A : (ℝ × ℝ) → V →L[ℝ] (ℝ × ℝ)) (p : ℝ × ℝ)
    (hD : ContinuousAt D p) (hA : ContinuousAt A p)
    (hinj : Function.Injective ((A p).comp (D p)))
    {M M₀ : ℝ} (hM : 0 ≤ M) (hM₀ : 0 ≤ M₀) :
    ∃ r ε : ℝ, 0 < r ∧ 0 < ε ∧
      ∀ (f : (ℝ × ℝ) → V) (df : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] V),
        (∀ q ∈ Metric.ball p r, HasFDerivWithinAt f (df q) (Metric.ball p r) q) →
        (∀ q ∈ Metric.ball p r, ‖df q‖ ≤ M) →
        (∀ q ∈ Metric.ball p r, ‖D q‖ ≤ M₀) →
        (∀ q ∈ Metric.ball p r, ∃ w : V, A q w = 0 ∧
          ‖df q (1, 0) - D q (1, 0) - w‖ ≤ ε ∧
          ‖df q (0, 1) - D q (0, 1)‖ ≤ ε) →
        Set.InjOn f (Metric.ball p r) := by
  classical
  obtain ⟨r, ρ, hr, hρ, hall⟩ := exists_injective_ball_of_testing_transversality
    D A p hD hA hinj (B := M + M₀ + 1) (by linarith)
  let ε := min ρ 1 / 2
  have hε : 0 < ε := half_pos (lt_min hρ zero_lt_one)
  have hερ : 2 * ε ≤ ρ := by dsimp [ε]; linarith [min_le_left ρ 1]
  have hεone : 2 * ε ≤ 1 := by dsimp [ε]; linarith [min_le_right ρ 1]
  refine ⟨r, ε, hr, hε, ?_⟩
  intro f df hf hdf hold hprofiles
  have hexists : ∀ q, ∃ w : V, q ∈ Metric.ball p r → A q w = 0 ∧
      ‖df q (1, 0) - D q (1, 0) - w‖ ≤ ε ∧
      ‖df q (0, 1) - D q (0, 1)‖ ≤ ε := by
    intro q
    by_cases hq : q ∈ Metric.ball p r
    · obtain ⟨w, hw⟩ := hprofiles q hq
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h => False.elim (hq h)⟩
  choose w hw using hexists
  have hresidual (q) (hq : q ∈ Metric.ball p r) :
      ‖df q - D q - coordinateTransverseMap (w q)‖ ≤ 2 * ε :=
    residual_bound_of_two_coordinate_profiles (df q) (D q) (w q)
      (hw q hq).2.1 (hw q hq).2.2
  apply hall f df (fun q => coordinateTransverseMap (w q)) hf
  · intro q hq
    exact coordinateTransverseMap_killed (A q) (hw q hq).1
  · intro q hq
    exact (transverse_norm_bound_of_exact_derivative (df q) (D q) _
      (hdf q hq) (hold q hq) (hresidual q hq)).trans (by linarith)
  · intro q hq
    exact (hresidual q hq).trans hερ

end R4Embedding
