import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Ring

/-! The algebraic core of transversality. In surface coordinates, `u = F_x`,
`v = F_y`, `acc = F_yy`, and `k` is the nonzero Christoffel coefficient. -/

namespace R4Embedding

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A tangent vector perpendicular to `F_y` and `F_yy` vanishes when the
coefficient of `F_x` in the tangential part of `F_yy` is nonzero. -/
theorem transverse_orthogonal_intersection
    {u v acc normal w : V} {k l a b : ℝ}
    (hacc : acc = k • u + l • v + normal) (hk : k ≠ 0)
    (hnu : inner ℝ u normal = 0) (hnv : inner ℝ v normal = 0)
    (hw : w = a • u + b • v)
    (hwv : inner ℝ w v = 0) (hwacc : inner ℝ w acc = 0) : w = 0 := by
  have hwn : inner ℝ w normal = 0 := by
    rw [hw, inner_add_left, real_inner_smul_left, real_inner_smul_left, hnu, hnv]
    simp
  have hwu : inner ℝ w u = 0 := by
    rw [hacc, inner_add_right, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, hwv, hwn] at hwacc
    have hmul : k * inner ℝ w u = 0 := by simpa using hwacc
    exact (mul_eq_zero.mp hmul).resolve_left hk
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  calc
    inner ℝ w w = inner ℝ w (a • u + b • v) := congrArg (inner ℝ w) hw
    _ = 0 := by rw [inner_add_right, real_inner_smul_right,
      real_inner_smul_right, hwu, hwv]; simp

/-- The pairing determinant is `-k` times the Gram determinant. -/
theorem transverse_pairing_determinant
    {u v acc normal : V} {k l : ℝ}
    (hacc : acc = k • u + l • v + normal)
    (hnu : inner ℝ normal u = 0) (hnv : inner ℝ normal v = 0) :
    inner ℝ v u * inner ℝ acc v - inner ℝ v v * inner ℝ acc u =
      -k * (inner ℝ u u * inner ℝ v v - (inner ℝ u v) ^ 2) := by
  rw [hacc]
  simp only [inner_add_left, real_inner_smul_left, hnu, hnv, add_zero]
  rw [real_inner_comm v u]
  ring

end R4Embedding
