import R4Embedding.ProjectedDerivative

/-! The first two entries of the five-profile vector are the two coordinate
derivatives. Their pointwise errors control the full operator norm. The exact
correction is added to the residual of the same approximate map. -/

namespace R4Embedding

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem coordinate_operator_norm_bound
    (T : (ℝ × ℝ) →L[ℝ] V) {a b : ℝ}
    (h₀ : ‖T (1, 0)‖ ≤ a) (h₁ : ‖T (0, 1)‖ ≤ b) : ‖T‖ ≤ a + b := by
  have ha : 0 ≤ a := (norm_nonneg _).trans h₀
  have hb : 0 ≤ b := (norm_nonneg _).trans h₁
  apply T.opNorm_le_bound (add_nonneg ha hb)
  intro x
  have heq : T x = x.1 • T (1, 0) + x.2 • T (0, 1) := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
  rw [heq]
  calc
    ‖x.1 • T (1, 0) + x.2 • T (0, 1)‖ ≤ ‖x.1 • T (1, 0)‖ + ‖x.2 • T (0, 1)‖ :=
      norm_add_le _ _
    _ = ‖x.1‖ * ‖T (1, 0)‖ + ‖x.2‖ * ‖T (0, 1)‖ := by rw [norm_smul, norm_smul]
    _ ≤ ‖x‖ * a + ‖x‖ * b := add_le_add
      (mul_le_mul (norm_fst_le x) h₀ (norm_nonneg _) (norm_nonneg _))
      (mul_le_mul (norm_snd_le x) h₁ (norm_nonneg _) (norm_nonneg _))
    _ = (a + b) * ‖x‖ := by ring

/-- A bound on the first two entries of one profile controls the same map's
derivative. The other three entries remain available for boundary geometry. -/
theorem operator_norm_bound_of_profile
    (T : (ℝ × ℝ) →L[ℝ] V) (profile : Fin 5 → V) {ε : ℝ}
    (h₀ : profile 0 = T (1, 0)) (h₁ : profile 1 = T (0, 1))
    (hprofile : ‖profile‖ ≤ ε) : ‖T‖ ≤ 2 * ε := by
  have hzero : ‖T (1, 0)‖ ≤ ε := by
    rw [← h₀]
    exact (norm_le_pi_norm profile 0).trans hprofile
  have hone : ‖T (0, 1)‖ ≤ ε := by
    rw [← h₁]
    exact (norm_le_pi_norm profile 1).trans hprofile
  simpa only [two_mul] using coordinate_operator_norm_bound T hzero hone

/-- A small correction is added to the profile residual of the *same* map. -/
theorem corrected_derivative_residual_bound
    (exactD approximateD old transverse : E →L[ℝ] V) {ε δ : ℝ}
    (hprofile : ‖approximateD - old - transverse‖ ≤ ε)
    (hcorrection : ‖exactD - approximateD‖ ≤ δ) :
    ‖exactD - old - transverse‖ ≤ ε + δ := by
  have heq : exactD - old - transverse =
      (approximateD - old - transverse) + (exactD - approximateD) := by abel
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add hprofile hcorrection)

/-- Uniform boundedness of the exact derivative bounds the transverse term,
so it need not be bounded by a separate construction. -/
theorem transverse_norm_bound_of_exact_derivative
    (df old transverse : E →L[ℝ] V) {M M₀ ρ : ℝ}
    (hdf : ‖df‖ ≤ M) (hold : ‖old‖ ≤ M₀)
    (hresidual : ‖df - old - transverse‖ ≤ ρ) :
    ‖transverse‖ ≤ M + M₀ + ρ := by
  have heq : transverse = (df - old) - (df - old - transverse) := by abel
  calc
    ‖transverse‖ = ‖(df - old) - (df - old - transverse)‖ := congrArg norm heq
    _ ≤ ‖df - old‖ + ‖df - old - transverse‖ := norm_sub_le _ _
    _ ≤ (‖df‖ + ‖old‖) + ‖df - old - transverse‖ :=
      add_le_add (norm_sub_le df old) (le_refl _)
    _ ≤ M + M₀ + ρ := add_le_add (add_le_add hdf hold) hresidual

end R4Embedding
