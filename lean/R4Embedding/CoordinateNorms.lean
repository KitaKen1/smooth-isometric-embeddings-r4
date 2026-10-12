import R4Embedding.Problem
import R4Embedding.PrimitiveInjectivity
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Real four-component profiles use a supremum norm; four-space uses the
Euclidean norm. The coordinate identity is a continuous linear equivalence,
with norm loss at most 2. Dot-product orthogonality is preserved. -/

noncomputable section

namespace R4Embedding

abbrev RawVector := Fin 4 → ℝ

def rawToSpace : RawVector ≃L[ℝ] Space :=
  (WithLp.linearEquiv 2 ℝ RawVector).symm.toContinuousLinearEquiv

theorem rawToSpace_apply (x : RawVector) (i : Fin 4) : rawToSpace x i = x i := rfl

theorem rawToSpace_inner (x y : RawVector) :
    inner ℝ (rawToSpace x) (rawToSpace y) = ∑ i, x i * y i := by
  change inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y) = _
  simpa only [star_trivial, dotProduct, mul_comm] using
    (EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) x y)

theorem norm_rawToSpace_le (x : RawVector) : ‖rawToSpace x‖ ≤ 2 * ‖x‖ := by
  have hsq : ‖rawToSpace x‖ ^ 2 ≤ 4 * ‖x‖ ^ 2 := by
    calc
      ‖rawToSpace x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        rfl
      _ ≤ ∑ _i : Fin 4, ‖x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith [norm_le_pi_norm x i, norm_nonneg (x i), norm_nonneg x]
      _ = 4 * ‖x‖ ^ 2 := by simp
  nlinarith [norm_nonneg (rawToSpace x), norm_nonneg x]

theorem rawToSpace_profile_bound (J : Fin 5 → RawVector) {ε : ℝ} (hJ : ‖J‖ ≤ ε) :
    ‖fun i => rawToSpace (J i)‖ ≤ 2 * ε := by
  have hε : 0 ≤ ε := (norm_nonneg J).trans hJ
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) hε)).mpr
  intro i
  exact (norm_rawToSpace_le (J i)).trans
    (mul_le_mul_of_nonneg_left ((norm_le_pi_norm J i).trans hJ) (by norm_num))

theorem rawToSpace_orthogonal {x y : RawVector} (hxy : ∑ i, x i * y i = 0) :
    inner ℝ (rawToSpace x) (rawToSpace y) = 0 := by
  rw [rawToSpace_inner, hxy]

/-- An operator estimate for the actual raw coordinate read gives the
Euclidean operator estimate needed on exterior chart balls. -/
theorem norm_le_twice_of_raw_coordinate_read {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] Space) {ε : ℝ}
    (hread : ‖rawToSpace.symm.toContinuousLinearMap.comp L‖ ≤ ε) :
    ‖L‖ ≤ 2 * ε := by
  let R := rawToSpace.symm.toContinuousLinearMap.comp L
  have hε : 0 ≤ ε := (norm_nonneg R).trans hread
  apply L.opNorm_le_bound (mul_nonneg (by norm_num) hε)
  intro x
  calc
    ‖L x‖ = ‖rawToSpace (R x)‖ := by simp only [R,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply]
    _ ≤ 2 * ‖R x‖ := norm_rawToSpace_le _
    _ ≤ 2 * (‖R‖ * ‖x‖) := mul_le_mul_of_nonneg_left (R.le_opNorm x) (by norm_num)
    _ ≤ 2 * (ε * ‖x‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hread (norm_nonneg x)) (by norm_num)
    _ = (2 * ε) * ‖x‖ := by ring

/-- The real-vector errors of an exact output yield an ordinary Euclidean
operator residual, with explicit loss 4 rather than an assumed isometry. -/
theorem residual_bound_of_raw_coordinate_profiles
    (df old : (ℝ × ℝ) →L[ℝ] Space) (w : RawVector) {ε : ℝ}
    (hx : ‖rawToSpace.symm (df (1, 0) - old (1, 0)) - w‖ ≤ ε)
    (hy : ‖rawToSpace.symm (df (0, 1) - old (0, 1))‖ ≤ ε) :
    ‖df - old - coordinateTransverseMap (rawToSpace w)‖ ≤ 4 * ε := by
  have hx' : ‖df (1, 0) - old (1, 0) - rawToSpace w‖ ≤ 2 * ε := by
    have h := (norm_rawToSpace_le (rawToSpace.symm (df (1, 0) - old (1, 0)) - w)).trans
      (mul_le_mul_of_nonneg_left hx (by norm_num : (0 : ℝ) ≤ 2))
    simpa only [map_sub, ContinuousLinearEquiv.apply_symm_apply] using h
  have hy' : ‖df (0, 1) - old (0, 1)‖ ≤ 2 * ε := by
    have h := (norm_rawToSpace_le (rawToSpace.symm (df (0, 1) - old (0, 1)))).trans
      (mul_le_mul_of_nonneg_left hy (by norm_num : (0 : ℝ) ≤ 2))
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using h
  exact (residual_bound_of_two_coordinate_profiles df old (rawToSpace w) hx' hy').trans_eq (by ring)

end R4Embedding
