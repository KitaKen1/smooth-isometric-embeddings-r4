import R4Embedding.InitialPolynomialModel
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Tactic.Ring

/-! The concrete polynomial level as two continuous graphs over a planar
region. These topological coordinates are not smooth coordinates at their
common zero-height locus. Genus and supplied-atlas classification remain
separate obligations. -/

set_option autoImplicit false
noncomputable section
namespace R4Embedding

open Finset
open scoped ContDiff
attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup
  AddCommGroup.toAddCommMonoid NormedSpace.toModule

abbrev ModelBase := Fin 2 → ℝ

def modelHeightPoint (q : ModelBase) (z : ℝ) : ModelAmbient := ![q 0, q 1, z]
def modelPlanarProjection (p : ModelAmbient) : ModelBase := ![p 0, p 1]
def modelPlanarProduct (g : ℕ) (q : ModelBase) : ℝ :=
  ∏ i ∈ range (g + 1), modelFactor g i (modelHeightPoint q 0)
def modelPlanarRegion (g : ℕ) : Set ModelBase :=
  {q | modelFactor g 0 (modelHeightPoint q 0) ≤ 0 ∧
    ∀ i ∈ range (g + 1), i ≠ 0 → 0 ≤ modelFactor g i (modelHeightPoint q 0)}

theorem model_inner_positive_on_distinct_closed_disk {g i j : ℕ}
    (hi0 : i ≠ 0) (hj0 : j ≠ 0) (hij : i ≠ j) {p : ModelAmbient}
    (hi : modelFactor g i p ≤ 0) : 0 < modelFactor g j p := by
  by_contra hj
  have hjle : modelFactor g j p ≤ 0 := le_of_not_gt hj
  simp only [modelFactor, ite_eq_right hi0, ite_eq_right hj0] at hi hjle
  obtain ⟨hilo, hihi, _⟩ := model_inner_coordinate_bounds hi
  obtain ⟨hjlo, hjhi, _⟩ := model_inner_coordinate_bounds hjle
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hsep : (i : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.succ_le_of_lt hlt)
    linarith
  · have hsep : (j : ℝ) + 1 ≤ i := by exact_mod_cast (Nat.succ_le_of_lt hgt)
    linarith

theorem model_factor_product_nonpos_iff (g : ℕ) (p : ModelAmbient) :
    (∏ i ∈ range (g + 1), modelFactor g i p) ≤ 0 ↔
      modelFactor g 0 p ≤ 0 ∧
      ∀ i ∈ range (g + 1), i ≠ 0 → 0 ≤ modelFactor g i p := by
  have hzero : 0 ∈ range (g + 1) := by simp
  constructor
  · intro hprod
    have hout : modelFactor g 0 p ≤ 0 := by
      by_contra h
      have houter : 0 < modelFactor g 0 p := lt_of_not_ge h
      have hpositive : 0 < ∏ i ∈ range (g + 1), modelFactor g i p := by
        apply prod_pos
        intro i hi
        by_cases hi0 : i = 0
        · simpa [hi0] using houter
        · by_contra hinner
          have hn := model_outer_negative_on_inner hi hi0
            (by simpa [modelFactor, ite_eq_right hi0] using le_of_not_gt hinner)
          linarith
      linarith
    refine ⟨hout, ?_⟩
    intro i hi hi0
    by_contra h
    have hinner : modelFactor g i p < 0 := lt_of_not_ge h
    have houter : modelFactor g 0 p < 0 := model_outer_negative_on_inner hi hi0
      (by simpa [modelFactor, ite_eq_right hi0] using hinner.le)
    have hiErase : i ∈ (range (g + 1)).erase 0 := mem_erase.mpr ⟨hi0, hi⟩
    have hremaining : 0 < ∏ j ∈ ((range (g + 1)).erase 0).erase i, modelFactor g j p := by
      apply prod_pos
      intro j hj
      have hj0 := (mem_erase.mp (mem_erase.mp hj).2).1
      exact model_inner_positive_on_distinct_closed_disk hi0 hj0
        (mem_erase.mp hj).1.symm hinner.le
    have heq : (∏ j ∈ range (g + 1), modelFactor g j p) =
        modelFactor g 0 p * (modelFactor g i p *
          ∏ j ∈ ((range (g + 1)).erase 0).erase i, modelFactor g j p) := by
      rw [← mul_prod_erase _ (fun j => modelFactor g j p) hzero,
        ← mul_prod_erase _ (fun j => modelFactor g j p) hiErase]
    have hpositive : 0 < ∏ j ∈ range (g + 1), modelFactor g j p := by
      rw [heq]
      exact mul_pos_of_neg_of_neg houter (mul_neg_of_neg_of_pos hinner hremaining)
    linarith
  · rintro ⟨hout, hinner⟩
    rw [← mul_prod_erase _ (fun j => modelFactor g j p) hzero]
    apply mul_nonpos_of_nonpos_of_nonneg hout
    apply prod_nonneg
    intro i hi
    exact hinner i (mem_erase.mp hi).2 (mem_erase.mp hi).1

theorem modelFactor_heightPoint (g i : ℕ) (q : ModelBase) (z : ℝ) :
    modelFactor g i (modelHeightPoint q z) = modelFactor g i (modelHeightPoint q 0) := by
  simp [modelFactor, modelCircleFactor, modelHeightPoint]

theorem modelPolynomial_heightPoint (g : ℕ) (q : ModelBase) (z : ℝ) :
    modelPolynomial g (modelHeightPoint q z) = modelPlanarProduct g q + z ^ 2 := by
  simp [modelPolynomial, modelPlanarProduct, modelHeightPoint,
    modelFactor, modelCircleFactor]

theorem modelHeightPoint_projection (p : ModelAmbient) :
    modelHeightPoint (modelPlanarProjection p) (p 2) = p := by
  ext i
  fin_cases i <;> simp [modelHeightPoint, modelPlanarProjection]

theorem modelPlanarProjection_heightPoint (q : ModelBase) (z : ℝ) :
    modelPlanarProjection (modelHeightPoint q z) = q := by
  ext i
  fin_cases i <;> simp [modelHeightPoint, modelPlanarProjection]

theorem modelPlanarProduct_nonpos_iff (g : ℕ) (q : ModelBase) :
    modelPlanarProduct g q ≤ 0 ↔ q ∈ modelPlanarRegion g :=
  model_factor_product_nonpos_iff g (modelHeightPoint q 0)

theorem modelPolynomial_zero_projection_region (g : ℕ) {p : ModelAmbient}
    (hp : modelPolynomial g p = 0) : modelPlanarProjection p ∈ modelPlanarRegion g := by
  have h : modelPlanarProduct g (modelPlanarProjection p) + (p 2) ^ 2 = 0 := by
    rw [← modelPolynomial_heightPoint, modelHeightPoint_projection]
    exact hp
  apply (modelPlanarProduct_nonpos_iff g _).mp
  nlinarith [sq_nonneg (p 2)]

theorem continuous_modelHeightPoint {h : ModelBase → ℝ} (hh : Continuous h) :
    Continuous (fun q => modelHeightPoint q (h q)) := by
  apply continuous_pi
  intro i
  fin_cases i
  · simpa [modelHeightPoint] using (continuous_apply (0 : Fin 2))
  · simpa [modelHeightPoint] using (continuous_apply (1 : Fin 2))
  · simpa [modelHeightPoint] using hh

theorem continuous_modelPlanarProjection : Continuous modelPlanarProjection := by
  apply continuous_pi
  intro i
  fin_cases i
  · simpa [modelPlanarProjection] using (continuous_apply (0 : Fin 3))
  · simpa [modelPlanarProjection] using (continuous_apply (1 : Fin 3))

theorem continuous_modelPlanarProduct (g : ℕ) : Continuous (modelPlanarProduct g) := by
  have hP : ContDiff ℝ ∞ (fun p : ModelAmbient =>
      ∏ i ∈ range (g + 1), modelFactor g i p) :=
    contDiff_prod fun i _ => modelCircleFactor_contDiff _ _
  exact hP.continuous.comp (continuous_modelHeightPoint continuous_const)

def modelUpperPoint (g : ℕ) (q : ModelBase) : ModelAmbient :=
  modelHeightPoint q (Real.sqrt (-modelPlanarProduct g q))
def modelLowerPoint (g : ℕ) (q : ModelBase) : ModelAmbient :=
  modelHeightPoint q (-Real.sqrt (-modelPlanarProduct g q))

theorem continuous_modelUpperPoint (g : ℕ) : Continuous (modelUpperPoint g) :=
  continuous_modelHeightPoint (Real.continuous_sqrt.comp (continuous_modelPlanarProduct g).neg)

theorem continuous_modelLowerPoint (g : ℕ) : Continuous (modelLowerPoint g) :=
  continuous_modelHeightPoint (Real.continuous_sqrt.comp (continuous_modelPlanarProduct g).neg).neg

theorem modelUpperPoint_zero (g : ℕ) {q : ModelBase} (hq : q ∈ modelPlanarRegion g) :
    modelPolynomial g (modelUpperPoint g q) = 0 := by
  have hn : 0 ≤ -modelPlanarProduct g q :=
    neg_nonneg.mpr ((modelPlanarProduct_nonpos_iff g q).mpr hq)
  simp [modelUpperPoint, modelPolynomial_heightPoint, Real.sq_sqrt hn]

theorem modelLowerPoint_zero (g : ℕ) {q : ModelBase} (hq : q ∈ modelPlanarRegion g) :
    modelPolynomial g (modelLowerPoint g q) = 0 := by
  have hn : 0 ≤ -modelPlanarProduct g q :=
    neg_nonneg.mpr ((modelPlanarProduct_nonpos_iff g q).mpr hq)
  simp [modelLowerPoint, modelPolynomial_heightPoint, Real.sq_sqrt hn]

theorem modelUpperPoint_recover (g : ℕ) {p : ModelAmbient}
    (hp : modelPolynomial g p = 0) (hz : 0 ≤ p 2) :
    modelUpperPoint g (modelPlanarProjection p) = p := by
  have h : modelPlanarProduct g (modelPlanarProjection p) + (p 2) ^ 2 = 0 := by
    rw [← modelPolynomial_heightPoint, modelHeightPoint_projection]
    exact hp
  have heq : -modelPlanarProduct g (modelPlanarProjection p) = (p 2) ^ 2 := by linarith
  unfold modelUpperPoint
  rw [heq, Real.sqrt_sq hz, modelHeightPoint_projection]

theorem modelLowerPoint_recover (g : ℕ) {p : ModelAmbient}
    (hp : modelPolynomial g p = 0) (hz : p 2 ≤ 0) :
    modelLowerPoint g (modelPlanarProjection p) = p := by
  have h : modelPlanarProduct g (modelPlanarProjection p) + (p 2) ^ 2 = 0 := by
    rw [← modelPolynomial_heightPoint, modelHeightPoint_projection]
    exact hp
  have heq : -modelPlanarProduct g (modelPlanarProjection p) = (p 2) ^ 2 := by linarith
  have hsq : Real.sqrt ((p 2) ^ 2) = -p 2 := by
    simpa only [neg_sq] using Real.sqrt_sq (neg_nonneg.mpr hz)
  unfold modelLowerPoint
  rw [heq, hsq, neg_neg, modelHeightPoint_projection]

theorem modelPolynomial_zero_iff_graphs (g : ℕ) (p : ModelAmbient) :
    modelPolynomial g p = 0 ↔
      ∃ q ∈ modelPlanarRegion g, p = modelUpperPoint g q ∨ p = modelLowerPoint g q := by
  constructor
  · intro hp
    refine ⟨modelPlanarProjection p, modelPolynomial_zero_projection_region g hp, ?_⟩
    rcases le_total 0 (p 2) with hz | hz
    · exact Or.inl (modelUpperPoint_recover g hp hz).symm
    · exact Or.inr (modelLowerPoint_recover g hp hz).symm
  · rintro ⟨q, hq, h | h⟩
    · rw [h]
      exact modelUpperPoint_zero g hq
    · rw [h]
      exact modelLowerPoint_zero g hq

theorem modelUpperPoint_eq_lowerPoint_iff (g : ℕ) {q : ModelBase}
    (hq : q ∈ modelPlanarRegion g) :
    modelUpperPoint g q = modelLowerPoint g q ↔ modelPlanarProduct g q = 0 := by
  have hn : 0 ≤ -modelPlanarProduct g q :=
    neg_nonneg.mpr ((modelPlanarProduct_nonpos_iff g q).mpr hq)
  constructor
  · intro h
    have hz := congrArg (fun p : ModelAmbient => p 2) h
    change Real.sqrt (-modelPlanarProduct g q) = -Real.sqrt (-modelPlanarProduct g q) at hz
    have hs : Real.sqrt (-modelPlanarProduct g q) = 0 := by linarith
    have hsq := Real.sq_sqrt hn
    rw [hs] at hsq
    linarith
  · intro h
    simp [modelUpperPoint, modelLowerPoint, h]

theorem modelPlanarProduct_zero_iff_circles (g : ℕ) (q : ModelBase) :
    modelPlanarProduct g q = 0 ↔
      ∃ i ∈ range (g + 1), modelFactor g i (modelHeightPoint q 0) = 0 :=
  prod_eq_zero_iff

theorem modelPlanarRegion_iff_disk_holes (g : ℕ) (q : ModelBase) :
    q ∈ modelPlanarRegion g ↔
      (q 0) ^ 2 + (q 1) ^ 2 ≤ (modelRadius g) ^ 2 ∧
      ∀ i ∈ range (g + 1), i ≠ 0 → 1 ≤ (q 0 - 3 * (i : ℝ)) ^ 2 + (q 1) ^ 2 := by
  constructor
  · rintro ⟨hout, hinner⟩
    constructor
    · simpa [modelFactor, modelCircleFactor, modelHeightPoint, sub_nonpos] using hout
    · intro i hi hi0
      simpa [modelFactor, modelCircleFactor, modelHeightPoint, ite_eq_right hi0,
        sub_nonneg] using hinner i hi hi0
  · rintro ⟨hout, hinner⟩
    constructor
    · simpa [modelFactor, modelCircleFactor, modelHeightPoint, sub_nonpos] using hout
    · intro i hi hi0
      simpa [modelFactor, modelCircleFactor, modelHeightPoint, ite_eq_right hi0,
        sub_nonneg] using hinner i hi hi0

abbrev PlanarModelDomain (g : ℕ) := {q : ModelBase // q ∈ modelPlanarRegion g}
abbrev ModelUpperHalf (g : ℕ) :=
  {p : ModelAmbient // modelPolynomial g p = 0 ∧ 0 ≤ p 2}
abbrev ModelLowerHalf (g : ℕ) :=
  {p : ModelAmbient // modelPolynomial g p = 0 ∧ p 2 ≤ 0}

def modelUpperHomeomorph (g : ℕ) : PlanarModelDomain g ≃ₜ ModelUpperHalf g where
  toEquiv :=
    { toFun := fun q => ⟨modelUpperPoint g q, modelUpperPoint_zero g q.2,
        by simp [modelUpperPoint, modelHeightPoint]⟩
      invFun := fun p => ⟨modelPlanarProjection p, modelPolynomial_zero_projection_region g p.2.1⟩
      left_inv := fun q => Subtype.ext (modelPlanarProjection_heightPoint q
        (Real.sqrt (-modelPlanarProduct g q)))
      right_inv := fun p => Subtype.ext (modelUpperPoint_recover g p.2.1 p.2.2) }
  continuous_toFun := (continuous_modelUpperPoint g |>.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_modelPlanarProjection.comp continuous_subtype_val).subtype_mk _

def modelLowerHomeomorph (g : ℕ) : PlanarModelDomain g ≃ₜ ModelLowerHalf g where
  toEquiv :=
    { toFun := fun q => ⟨modelLowerPoint g q, modelLowerPoint_zero g q.2,
        by simp [modelLowerPoint, modelHeightPoint]⟩
      invFun := fun p => ⟨modelPlanarProjection p, modelPolynomial_zero_projection_region g p.2.1⟩
      left_inv := fun q => Subtype.ext (modelPlanarProjection_heightPoint q
        (-Real.sqrt (-modelPlanarProduct g q)))
      right_inv := fun p => Subtype.ext (modelLowerPoint_recover g p.2.1 p.2.2) }
  continuous_toFun := (continuous_modelLowerPoint g |>.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_modelPlanarProjection.comp continuous_subtype_val).subtype_mk _

theorem exists_modelUpperHomeomorph (g : ℕ) : Nonempty (PlanarModelDomain g ≃ₜ ModelUpperHalf g) :=
  ⟨modelUpperHomeomorph g⟩

theorem exists_modelLowerHomeomorph (g : ℕ) : Nonempty (PlanarModelDomain g ≃ₜ ModelLowerHalf g) :=
  ⟨modelLowerHomeomorph g⟩

/-! Explicit paths avoid all holes simultaneously: first decrease the
horizontal coordinate on a circle centered at zero, then follow the negative
horizontal axis to zero. No triangulation or finite obstacle algorithm is
required for connectedness. -/
open Set

def modelBaseRadius (q : ModelBase) : ℝ := Real.sqrt ((q 0) ^ 2 + (q 1) ^ 2)
def modelArcX (q : ModelBase) (t : ℝ) : ℝ :=
  (1 - t) * q 0 - t * modelBaseRadius q

def modelCircularArc (q : ModelBase) (t : ℝ) : ModelBase :=
  ![modelArcX q t,
    if 0 ≤ q 1 then Real.sqrt ((modelBaseRadius q) ^ 2 - (modelArcX q t) ^ 2)
    else -Real.sqrt ((modelBaseRadius q) ^ 2 - (modelArcX q t) ^ 2)]

def modelNegativeAxisPoint (q : ModelBase) (t : ℝ) : ModelBase :=
  ![-((1 - t) * modelBaseRadius q), 0]

theorem modelBaseRadius_nonneg (q : ModelBase) : 0 ≤ modelBaseRadius q := Real.sqrt_nonneg _

theorem modelBaseRadius_sq (q : ModelBase) :
    (modelBaseRadius q) ^ 2 = (q 0) ^ 2 + (q 1) ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem modelBaseRadius_coordinate_bounds (q : ModelBase) :
    |q 0| ≤ modelBaseRadius q ∧ |q 1| ≤ modelBaseRadius q := by
  have hs := modelBaseRadius_sq q
  constructor
  · apply abs_le_of_sq_le_sq _ (modelBaseRadius_nonneg q)
    nlinarith [sq_nonneg (q 1)]
  · apply abs_le_of_sq_le_sq _ (modelBaseRadius_nonneg q)
    nlinarith [sq_nonneg (q 0)]

theorem modelArcX_bounds (q : ModelBase) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    -modelBaseRadius q ≤ modelArcX q t ∧ modelArcX q t ≤ q 0 := by
  have hx := (abs_le.mp (modelBaseRadius_coordinate_bounds q).1).1
  have hsum : 0 ≤ q 0 + modelBaseRadius q := by linarith
  dsimp [modelArcX]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr ht1) hsum]
  · nlinarith [mul_nonneg ht0 hsum]

theorem modelCircularArc_radicand_nonneg (q : ModelBase) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ (modelBaseRadius q) ^ 2 - (modelArcX q t) ^ 2 := by
  obtain ⟨hlo, hhi⟩ := modelArcX_bounds q ht0 ht1
  have hx := (abs_le.mp (modelBaseRadius_coordinate_bounds q).1).2
  have hleft : 0 ≤ modelBaseRadius q - modelArcX q t := by linarith
  have hright : 0 ≤ modelBaseRadius q + modelArcX q t := by linarith
  nlinarith [mul_nonneg hleft hright]

theorem modelCircularArc_norm_sq (q : ModelBase) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (modelCircularArc q t 0) ^ 2 + (modelCircularArc q t 1) ^ 2 = (modelBaseRadius q) ^ 2 := by
  have hs := Real.sq_sqrt (modelCircularArc_radicand_nonneg q ht0 ht1)
  change (modelArcX q t) ^ 2 +
    (if 0 ≤ q 1 then Real.sqrt ((modelBaseRadius q) ^ 2 - (modelArcX q t) ^ 2)
      else -Real.sqrt ((modelBaseRadius q) ^ 2 - (modelArcX q t) ^ 2)) ^ 2 = _
  split_ifs
  · linarith
  · rw [neg_sq]
    linarith

theorem modelCircularArc_zero (q : ModelBase) : modelCircularArc q 0 = q := by
  have hd : (modelBaseRadius q) ^ 2 - (q 0) ^ 2 = (q 1) ^ 2 := by
    nlinarith [modelBaseRadius_sq q]
  ext i
  fin_cases i
  · simp [modelCircularArc, modelArcX]
  · by_cases hy : 0 ≤ q 1
    · simp [modelCircularArc, modelArcX, hy, hd, Real.sqrt_sq hy]
    · simp [modelCircularArc, modelArcX, hy, hd, Real.sqrt_sq_eq_abs,
        abs_of_neg (lt_of_not_ge hy)]

theorem modelCircularArc_one (q : ModelBase) :
    modelCircularArc q 1 = ![-modelBaseRadius q, 0] := by
  ext i
  fin_cases i <;> simp [modelCircularArc, modelArcX]

theorem continuous_modelCircularArc (q : ModelBase) : Continuous (modelCircularArc q) := by
  have hx : Continuous (modelArcX q) :=
    ((continuous_const.sub continuous_id).mul continuous_const).sub
      (continuous_id.mul continuous_const)
  have hy : Continuous (fun t => Real.sqrt ((modelBaseRadius q) ^ 2 - (modelArcX q t) ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_const.sub (hx.pow 2))
  apply continuous_pi
  intro i
  fin_cases i
  · simpa [modelCircularArc] using hx
  · by_cases h : 0 ≤ q 1
    · simpa [modelCircularArc, h] using hy
    · simpa [modelCircularArc, h] using hy.fun_neg

theorem modelCircularArc_mem_region (g : ℕ) {q : ModelBase}
    (hq : q ∈ modelPlanarRegion g) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    modelCircularArc q t ∈ modelPlanarRegion g := by
  obtain ⟨hout, hinner⟩ := (modelPlanarRegion_iff_disk_holes g q).mp hq
  apply (modelPlanarRegion_iff_disk_holes g _).mpr
  have hs := modelCircularArc_norm_sq q ht0 ht1
  have hr := modelBaseRadius_sq q
  constructor
  · linarith
  · intro i hi hi0
    have hp := hinner i hi hi0
    have hx : modelCircularArc q t 0 ≤ q 0 := by
      simpa [modelCircularArc] using (modelArcX_bounds q ht0 ht1).2
    have hmonotone := mul_nonneg (show (0 : ℝ) ≤ 6 * (i : ℝ) by positivity)
      (sub_nonneg.mpr hx)
    nlinarith

theorem continuous_modelNegativeAxisPoint (q : ModelBase) :
    Continuous (modelNegativeAxisPoint q) := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun t : ℝ => -((1 - t) * modelBaseRadius q))
    exact ((continuous_const.fun_sub continuous_id).fun_mul continuous_const).fun_neg
  · simpa [modelNegativeAxisPoint] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))

theorem modelNegativeAxisPoint_zero (q : ModelBase) :
    modelNegativeAxisPoint q 0 = ![-modelBaseRadius q, 0] := by
  simp [modelNegativeAxisPoint]

theorem modelNegativeAxisPoint_one (q : ModelBase) :
    modelNegativeAxisPoint q 1 = 0 := by
  ext i
  fin_cases i <;> simp [modelNegativeAxisPoint]

theorem modelNegativeAxisPoint_mem_region (g : ℕ) {q : ModelBase}
    (hq : q ∈ modelPlanarRegion g) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    modelNegativeAxisPoint q t ∈ modelPlanarRegion g := by
  obtain ⟨hout, _⟩ := (modelPlanarRegion_iff_disk_holes g q).mp hq
  have hr := modelBaseRadius_sq q
  have hr0 := modelBaseRadius_nonneg q
  let a := (1 - t) * modelBaseRadius q
  have ha0 : 0 ≤ a := mul_nonneg (sub_nonneg.mpr ht1) hr0
  have har : a ≤ modelBaseRadius q := by
    dsimp [a]
    nlinarith [mul_nonneg ht0 hr0]
  apply (modelPlanarRegion_iff_disk_holes g _).mpr
  constructor
  · change (-a) ^ 2 + 0 ^ 2 ≤ (modelRadius g) ^ 2
    nlinarith [mul_nonneg (sub_nonneg.mpr har) (show 0 ≤ modelBaseRadius q + a by linarith)]
  · intro i _ hi0
    have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hi0)
    change 1 ≤ (-a - 3 * (i : ℝ)) ^ 2 + 0 ^ 2
    nlinarith [sq_nonneg (a + 3 * (i : ℝ) - 1)]

def modelCircularArcPath (q : ModelBase) : Path q (modelNegativeAxisPoint q 0) where
  toFun := fun t => modelCircularArc q t
  continuous_toFun := (continuous_modelCircularArc q).comp continuous_subtype_val
  source' := modelCircularArc_zero q
  target' := by simpa using (modelCircularArc_one q).trans (modelNegativeAxisPoint_zero q).symm

def modelNegativeAxisPath (q : ModelBase) : Path (modelNegativeAxisPoint q 0) 0 where
  toFun := fun t => modelNegativeAxisPoint q t
  continuous_toFun := (continuous_modelNegativeAxisPoint q).comp continuous_subtype_val
  source' := rfl
  target' := modelNegativeAxisPoint_one q

theorem modelPlanarRegion_origin (g : ℕ) : (0 : ModelBase) ∈ modelPlanarRegion g := by
  apply (modelPlanarRegion_iff_disk_holes g _).mpr
  constructor
  · change (0 : ℝ) ^ 2 + 0 ^ 2 ≤ (modelRadius g) ^ 2
    nlinarith [sq_nonneg (modelRadius g)]
  · intro i _ hi0
    have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hi0)
    change 1 ≤ (0 - 3 * (i : ℝ)) ^ 2 + 0 ^ 2
    nlinarith [sq_nonneg (3 * (i : ℝ) - 1)]

theorem modelPlanarRegion_joined_origin (g : ℕ) {q : ModelBase}
    (hq : q ∈ modelPlanarRegion g) : JoinedIn (modelPlanarRegion g) q 0 := by
  have ha : JoinedIn (modelPlanarRegion g) q (modelNegativeAxisPoint q 0) :=
    ⟨modelCircularArcPath q, fun t => modelCircularArc_mem_region g hq t.2.1 t.2.2⟩
  have hb : JoinedIn (modelPlanarRegion g) (modelNegativeAxisPoint q 0) 0 :=
    ⟨modelNegativeAxisPath q, fun t => modelNegativeAxisPoint_mem_region g hq t.2.1 t.2.2⟩
  exact ha.trans hb

theorem modelPlanarRegion_pathConnected (g : ℕ) : IsPathConnected (modelPlanarRegion g) :=
  ⟨0, modelPlanarRegion_origin g, fun _ hq => (modelPlanarRegion_joined_origin g hq).symm⟩

theorem modelLevel_eq_graph_images (g : ℕ) :
    {p : ModelAmbient | modelPolynomial g p = 0} =
      modelUpperPoint g '' modelPlanarRegion g ∪ modelLowerPoint g '' modelPlanarRegion g := by
  ext p
  change modelPolynomial g p = 0 ↔
    (∃ q ∈ modelPlanarRegion g, modelUpperPoint g q = p) ∨
      (∃ q ∈ modelPlanarRegion g, modelLowerPoint g q = p)
  rw [modelPolynomial_zero_iff_graphs]
  constructor
  · rintro ⟨q, hq, h | h⟩
    · exact Or.inl ⟨q, hq, h.symm⟩
    · exact Or.inr ⟨q, hq, h.symm⟩
  · rintro (⟨q, hq, h⟩ | ⟨q, hq, h⟩)
    · exact ⟨q, hq, Or.inl h.symm⟩
    · exact ⟨q, hq, Or.inr h.symm⟩

theorem modelPolynomial_level_pathConnected (g : ℕ) :
    IsPathConnected {p : ModelAmbient | modelPolynomial g p = 0} := by
  rw [modelLevel_eq_graph_images]
  have hupper := (modelPlanarRegion_pathConnected g).image (continuous_modelUpperPoint g)
  have hlower := (modelPlanarRegion_pathConnected g).image (continuous_modelLowerPoint g)
  let q : ModelBase := ![modelRadius g, 0]
  have hP : modelPlanarProduct g q = 0 := by
    apply Finset.prod_eq_zero (show 0 ∈ Finset.range (g + 1) by simp)
    simp [modelFactor, modelCircleFactor, modelHeightPoint, q]
  have hq := (modelPlanarProduct_nonpos_iff g q).mp hP.le
  have heq := (modelUpperPoint_eq_lowerPoint_iff g hq).mpr hP
  exact hupper.union hlower ⟨modelUpperPoint g q, ⟨q, hq, rfl⟩, ⟨q, hq, heq.symm⟩⟩

theorem modelPolynomial_level_pathConnectedSpace (g : ℕ) :
    PathConnectedSpace {p : ModelAmbient // modelPolynomial g p = 0} :=
  isPathConnected_iff_pathConnectedSpace.mp (modelPolynomial_level_pathConnected g)

end R4Embedding
