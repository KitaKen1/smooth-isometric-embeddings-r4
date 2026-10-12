import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

/-! A concrete polynomial family for candidate embedded surface models.
Regularity of the zero level does not identify its genus and does not prove
smooth classification of an arbitrary surface with its supplied atlas. -/

noncomputable section
namespace R4Embedding

open Manifold
open scoped ContDiff Manifold
open Finset

attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup
  AddCommGroup.toAddCommMonoid NormedSpace.toModule

abbrev ModelAmbient := Fin 3 → ℝ

def modelRadius (g : ℕ) : ℝ := 3 * (g + 1)

def modelCircleFactor (c r : ℝ) (p : ModelAmbient) : ℝ :=
  (p 0 - c) ^ 2 + (p 1) ^ 2 - r ^ 2

def modelFactor (g i : ℕ) : ModelAmbient → ℝ :=
  modelCircleFactor (3 * i) (if i = 0 then modelRadius g else 1)

def modelPolynomial (g : ℕ) (p : ModelAmbient) : ℝ :=
  (∏ i ∈ range (g + 1), modelFactor g i p) + (p 2) ^ 2

def modelCircleDerivative (c : ℝ) (p : ModelAmbient) : ModelAmbient →L[ℝ] ℝ :=
  (2 * (p 0 - c)) • ContinuousLinearMap.proj 0 +
    (2 * p 1) • ContinuousLinearMap.proj 1

theorem modelCircleFactor_contDiff (c r : ℝ) :
    ContDiff ℝ ∞ (modelCircleFactor c r) := by
  exact (((contDiff_apply ℝ ℝ 0).sub contDiff_const).pow 2).add
    ((contDiff_apply ℝ ℝ 1).pow 2) |>.sub contDiff_const

theorem modelCircleFactor_hasFDerivAt (c r : ℝ) (p : ModelAmbient) :
    HasFDerivAt (modelCircleFactor c r) (modelCircleDerivative c p) p := by
  convert ((((hasFDerivAt_apply (𝕜 := ℝ) 0 p).sub_const c).pow 2).add
      ((hasFDerivAt_apply (𝕜 := ℝ) 1 p).pow 2)).sub_const (r ^ 2) using 1 <;>
    first | rfl | simp [modelCircleDerivative]

theorem modelPolynomial_contDiff (g : ℕ) : ContDiff ℝ ∞ (modelPolynomial g) := by
  exact (contDiff_prod fun i _ => modelCircleFactor_contDiff _ _).add
    ((contDiff_apply ℝ ℝ 2).pow 2)

theorem modelRadius_pos (g : ℕ) : 0 < modelRadius g := by
  unfold modelRadius
  positivity

theorem model_inner_coordinate_bounds {i : ℕ} {p : ModelAmbient}
    (h : modelCircleFactor (3 * i) 1 p ≤ 0) :
    3 * (i : ℝ) - 1 ≤ p 0 ∧ p 0 ≤ 3 * (i : ℝ) + 1 ∧ (p 1) ^ 2 ≤ 1 := by
  dsimp [modelCircleFactor] at h
  constructor
  · nlinarith [sq_nonneg (p 1), sq_nonneg (p 0 - 3 * (i : ℝ) + 1)]
  constructor
  · nlinarith [sq_nonneg (p 1), sq_nonneg (p 0 - 3 * (i : ℝ) - 1)]
  · nlinarith [sq_nonneg (p 0 - 3 * (i : ℝ))]

theorem model_outer_negative_on_inner {g i : ℕ} (hi : i ∈ range (g + 1))
    (hi0 : i ≠ 0) {p : ModelAmbient} (h : modelCircleFactor (3 * i) 1 p ≤ 0) :
    modelFactor g 0 p < 0 := by
  obtain ⟨hxlo, hxhi, hy⟩ := model_inner_coordinate_bounds h
  have hig : (i : ℝ) ≤ g := by exact_mod_cast (Nat.le_of_lt_succ (mem_range.mp hi))
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hi0)
  have hx0 : 0 ≤ p 0 := by linarith
  have hxsq : (p 0) ^ 2 ≤ (3 * (g : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg (3 * (g : ℝ) + 1 - p 0)]
  simp only [modelFactor, modelCircleFactor, modelRadius, ite_true, Nat.cast_zero,
    mul_zero, sub_zero]
  nlinarith [show (0 : ℝ) ≤ g by positivity]

theorem model_inner_circles_disjoint {g i j : ℕ} (hi0 : i ≠ 0) (hj0 : j ≠ 0)
    (hij : i ≠ j) {p : ModelAmbient} (hi : modelFactor g i p = 0) :
    modelFactor g j p ≠ 0 := by
  intro hj
  simp only [modelFactor, ite_eq_right hi0, ite_eq_right hj0] at hi hj
  obtain ⟨hilo, hihi, _⟩ := model_inner_coordinate_bounds hi.le
  obtain ⟨hjlo, hjhi, _⟩ := model_inner_coordinate_bounds hj.le
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hsep : (i : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.succ_le_of_lt hlt)
    linarith
  · have hsep : (j : ℝ) + 1 ≤ i := by exact_mod_cast (Nat.succ_le_of_lt hgt)
    linarith

theorem model_zero_factor_unique {g i : ℕ} (hi : i ∈ range (g + 1))
    {p : ModelAmbient} (hzero : modelFactor g i p = 0) :
    ∀ j ∈ range (g + 1), j ≠ i → modelFactor g j p ≠ 0 := by
  intro j hj hji
  by_cases hi0 : i = 0
  · subst i
    intro hz
    have hn := model_outer_negative_on_inner hj hji
      (by simpa [modelFactor, ite_eq_right hji] using hz.le)
    linarith
  by_cases hj0 : j = 0
  · subst j
    exact ne_of_lt (model_outer_negative_on_inner hi hi0
      (by simpa [modelFactor, ite_eq_right hi0] using hzero.le))
  exact model_inner_circles_disjoint hi0 hj0 hji.symm hzero

theorem modelCircleDerivative_ne_zero {c r : ℝ} (hr : 0 < r) {p : ModelAmbient}
    (hz : modelCircleFactor c r p = 0) : modelCircleDerivative c p ≠ 0 := by
  intro hzero
  have hx := congrArg (fun L : ModelAmbient →L[ℝ] ℝ => L (Pi.single 0 1)) hzero
  have hy := congrArg (fun L : ModelAmbient →L[ℝ] ℝ => L (Pi.single 1 1)) hzero
  simp [modelCircleDerivative] at hx hy
  dsimp [modelCircleFactor] at hz
  nlinarith

theorem model_factor_radius_pos (g i : ℕ) :
    0 < (if i = 0 then modelRadius g else (1 : ℝ)) := by
  split_ifs
  · exact modelRadius_pos g
  · norm_num

theorem model_product_derivative_of_zero {g i : ℕ} (hi : i ∈ range (g + 1))
    {p : ModelAmbient} (hz : modelFactor g i p = 0) :
    fderiv ℝ (fun q => ∏ j ∈ range (g + 1), modelFactor g j q) p =
      (∏ j ∈ (range (g + 1)).erase i, modelFactor g j p) •
        modelCircleDerivative (3 * i) p := by
  have heq : (fun q => ∏ j ∈ range (g + 1), modelFactor g j q) =
      (fun q => modelFactor g i q *
        ∏ j ∈ (range (g + 1)).erase i, modelFactor g j q) := by
    funext q
    exact (mul_prod_erase _ (fun j => modelFactor g j q) hi).symm
  rw [heq]
  have hresSmooth : ContDiff ℝ ∞
      (fun q => ∏ j ∈ (range (g + 1)).erase i, modelFactor g j q) :=
    contDiff_prod fun j _ => modelCircleFactor_contDiff _ _
  have hres := hresSmooth.contDiffAt.differentiableAt (x := p) (by simp)
  have hfactor : HasFDerivAt (modelFactor g i) (modelCircleDerivative (3 * i) p) p :=
    modelCircleFactor_hasFDerivAt _ _ p
  simpa only [hz, zero_smul, zero_add] using
    (hfactor.fun_mul hres.hasFDerivAt).fderiv

theorem modelPolynomial_hasFDerivAt (g : ℕ) (p : ModelAmbient) :
    HasFDerivAt (modelPolynomial g)
      ((∑ i ∈ range (g + 1),
        (∏ j ∈ (range (g + 1)).erase i, modelFactor g j p) •
          modelCircleDerivative (3 * i) p) +
        (2 * p 2) • ContinuousLinearMap.proj 2) p := by
  convert ((HasFDerivAt.finsetProd (fun i (_ : i ∈ range (g + 1)) =>
      modelCircleFactor_hasFDerivAt (3 * i) (if i = 0 then modelRadius g else 1) p)).fun_add
        ((hasFDerivAt_apply (𝕜 := ℝ) 2 p).pow 2)) using 1 <;>
    first | rfl | simp [modelFactor]

theorem modelPolynomial_fderiv_vertical (g : ℕ) (p : ModelAmbient) :
    fderiv ℝ (modelPolynomial g) p (Pi.single 2 1) = 2 * p 2 := by
  rw [(modelPolynomial_hasFDerivAt g p).fderiv]
  simp [modelCircleDerivative]

theorem modelPolynomial_regular (g : ℕ) (p : ModelAmbient)
    (hz : modelPolynomial g p = 0) : fderiv ℝ (modelPolynomial g) p ≠ 0 := by
  by_cases hz2 : p 2 = 0
  · have hprod : ∏ i ∈ range (g + 1), modelFactor g i p = 0 := by
      simpa [modelPolynomial, hz2] using hz
    obtain ⟨i, hi, hzero⟩ := prod_eq_zero_iff.mp hprod
    have hres : (∏ j ∈ (range (g + 1)).erase i, modelFactor g j p) ≠ 0 := by
      apply prod_ne_zero_iff.mpr
      intro j hj
      exact model_zero_factor_unique hi hzero j (mem_erase.mp hj).2 (mem_erase.mp hj).1
    have hcircle := modelCircleDerivative_ne_zero (model_factor_radius_pos g i) hzero
    have hps : ContDiff ℝ ∞ (fun q => ∏ j ∈ range (g + 1), modelFactor g j q) :=
      contDiff_prod fun j _ => modelCircleFactor_contDiff _ _
    have hpd := hps.contDiffAt.differentiableAt (x := p) (by simp)
    have hpoly : fderiv ℝ (modelPolynomial g) p =
        fderiv ℝ (fun q => ∏ j ∈ range (g + 1), modelFactor g j q) p := by
      convert (hpd.hasFDerivAt.fun_add
        ((hasFDerivAt_apply (𝕜 := ℝ) 2 p).pow 2)).fderiv using 1 <;>
        first | rfl | simp [hz2]
    rw [hpoly, model_product_derivative_of_zero hi hzero]
    exact smul_ne_zero hres hcircle
  · intro hzero
    have hv := modelPolynomial_fderiv_vertical g p
    rw [hzero] at hv
    simp only [zero_apply] at hv
    exact hz2 (by linarith)

theorem modelPolynomial_outer_nonpos (g : ℕ) {p : ModelAmbient}
    (hz : modelPolynomial g p = 0) : modelFactor g 0 p ≤ 0 := by
  by_contra h
  have houter : 0 < modelFactor g 0 p := lt_of_not_ge h
  have hprod : 0 < ∏ i ∈ range (g + 1), modelFactor g i p := by
    apply prod_pos
    intro i hi
    by_cases hi0 : i = 0
    · simpa [hi0] using houter
    · by_contra hinner
      have hle : modelCircleFactor (3 * i) 1 p ≤ 0 := by
        simpa [modelFactor, ite_eq_right hi0] using le_of_not_gt hinner
      have hn := model_outer_negative_on_inner hi hi0 hle
      linarith
  dsimp [modelPolynomial] at hz
  nlinarith [sq_nonneg (p 2)]

theorem modelPolynomial_horizontal_bounds (g : ℕ) {p : ModelAmbient}
    (hz : modelPolynomial g p = 0) :
    |p 0| ≤ modelRadius g ∧ |p 1| ≤ modelRadius g := by
  have h := modelPolynomial_outer_nonpos g hz
  simp only [modelFactor, modelCircleFactor, ite_true, Nat.cast_zero,
    mul_zero, sub_zero] at h
  constructor
  · apply abs_le_of_sq_le_sq _ (modelRadius_pos g).le
    nlinarith [sq_nonneg (p 1)]
  · apply abs_le_of_sq_le_sq _ (modelRadius_pos g).le
    nlinarith [sq_nonneg (p 0)]

theorem modelPolynomial_level_compact (g : ℕ) :
    IsCompact {p : ModelAmbient | modelPolynomial g p = 0} := by
  let P : ModelAmbient → ℝ := fun q => ∏ i ∈ range (g + 1), modelFactor g i q
  have hP : ContDiff ℝ ∞ P := contDiff_prod fun i _ => modelCircleFactor_contDiff _ _
  obtain ⟨B, hB, hbound⟩ :=
    ((isCompact_closedBall (0 : ModelAmbient) (modelRadius g)).image
      hP.continuous).isBounded.exists_pos_norm_le
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq (modelPolynomial_contDiff g).continuous continuous_const
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨modelRadius g + B + 1, ?_⟩
  intro p hp
  obtain ⟨hx, hy⟩ := modelPolynomial_horizontal_bounds g hp
  let q : ModelAmbient := ![p 0, p 1, 0]
  have hq : q ∈ Metric.closedBall 0 (modelRadius g) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (modelRadius_pos g).le).mpr
    intro i
    fin_cases i
    · simpa [q, Real.norm_eq_abs] using hx
    · simpa [q, Real.norm_eq_abs] using hy
    · simpa [q] using (modelRadius_pos g).le
  have heq : P q = P p := by
    apply prod_congr rfl
    intro i _
    simp [modelFactor, modelCircleFactor, q]
  have hpbound : |P p| ≤ B := by
    simpa only [Real.norm_eq_abs, heq] using hbound (P q) ⟨q, hq, rfl⟩
  have hpeq : P p + (p 2) ^ 2 = 0 := hp
  have hzsq : (p 2) ^ 2 ≤ B := by
    have hneg := neg_le_abs (P p)
    linarith
  have hzabs : |p 2| ≤ B + 1 := by
    apply abs_le_of_sq_le_sq _ (by linarith)
    nlinarith [sq_nonneg B]
  apply (pi_norm_le_iff_of_nonneg (by have := modelRadius_pos g; linarith)).mpr
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · change |p 0| ≤ modelRadius g + B + 1
    linarith
  · change |p 1| ≤ modelRadius g + B + 1
    linarith
  · change |p 2| ≤ modelRadius g + B + 1
    have := modelRadius_pos g
    linarith

def modelOuterPoint (g : ℕ) : ModelAmbient := ![modelRadius g, 0, 0]

theorem modelPolynomial_level_nonempty (g : ℕ) :
    Set.Nonempty {p : ModelAmbient | modelPolynomial g p = 0} := by
  refine ⟨modelOuterPoint g, ?_⟩
  have houter : modelFactor g 0 (modelOuterPoint g) = 0 := by
    simp [modelFactor, modelCircleFactor, modelOuterPoint]
  have hprod : ∏ i ∈ range (g + 1), modelFactor g i (modelOuterPoint g) = 0 :=
    prod_eq_zero (show 0 ∈ range (g + 1) by simp) houter
  simpa [modelPolynomial, modelOuterPoint] using hprod

theorem modelPolynomial_contMDiff (g : ℕ) :
    ContMDiff 𝓘(ℝ, ModelAmbient) 𝓘(ℝ, ℝ) ∞ (modelPolynomial g) :=
  (modelPolynomial_contDiff g).contMDiff

theorem modelPolynomial_mfderiv_ne_zero (g : ℕ) (p : ModelAmbient)
    (hz : modelPolynomial g p = 0) :
    mfderiv 𝓘(ℝ, ModelAmbient) 𝓘(ℝ, ℝ) (modelPolynomial g) p ≠ 0 := by
  rw [mfderiv_eq_fderiv]
  exact modelPolynomial_regular g p hz

end R4Embedding
