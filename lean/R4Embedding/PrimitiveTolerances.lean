import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! A fixed finite-atlas error budget. This avoids choosing eighth roots
after the primitive output: a scale below min(1,delta) suffices. -/

namespace R4Embedding

theorem primitive_first_profile_budget {ε Dtotal D δ z : ℝ}
    (hε : 0 < ε) (hDtotal : 0 < Dtotal) (hD : 0 ≤ D) (hDDtotal : D ≤ Dtotal)
    (hδ : δ = ε / (4 * Dtotal)) (hz : 0 ≤ z) (hzsmall : z < min 1 δ) :
    2 * (D * (δ + z ^ 8)) ≤ ε := by
  have hδpos : 0 < δ := by
    rw [hδ]
    exact div_pos hε (mul_pos (by norm_num) hDtotal)
  have hz1 : z ≤ 1 := (le_of_lt hzsmall).trans (min_le_left _ _)
  have hzδ : z ≤ δ := (le_of_lt hzsmall).trans (min_le_right _ _)
  have hz8 : z ^ 8 ≤ δ := by
    calc
      z ^ 8 = z ^ 7 * z := by ring
      _ ≤ 1 * z := mul_le_mul_of_nonneg_right (pow_le_one₀ hz hz1) hz
      _ = z := one_mul _
      _ ≤ δ := hzδ
  have hδeq : 4 * Dtotal * δ = ε := by
    rw [hδ]
    field_simp [ne_of_gt hDtotal]
  calc
    2 * (D * (δ + z ^ 8)) ≤ 2 * (D * (δ + δ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl hz8) hD) (by norm_num)
    _ = 4 * D * δ := by ring
    _ ≤ 4 * Dtotal * δ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hDDtotal (by norm_num)) hδpos.le
    _ = ε := hδeq

end R4Embedding
