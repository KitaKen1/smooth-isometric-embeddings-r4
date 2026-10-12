import R4Embedding.InitialPolynomialModel
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Abel

/-! Actual smooth transverse vectors for the polynomial zero levels.
This is a step toward their coorientation. It does not yet construct the
surface orientation in the supplied tangent charts or identify the genus.
-/

set_option autoImplicit false
noncomputable section
namespace R4Embedding

open Finset
open scoped ContDiff

attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup
  AddCommGroup.toAddCommMonoid NormedSpace.toModule

def modelGradient (g : ℕ) (p : ModelAmbient) : ModelAmbient :=
  fun i => fderiv ℝ (modelPolynomial g) p (Pi.single i 1)

def modelNormalEnergy (g : ℕ) (p : ModelAmbient) : ℝ :=
  ∑ i : Fin 3, (modelGradient g p i) ^ 2

def modelTransverseVector (g : ℕ) (p : ModelAmbient) : ModelAmbient :=
  (modelNormalEnergy g p)⁻¹ • modelGradient g p

theorem modelGradient_contDiff (g : ℕ) : ContDiff ℝ ∞ (modelGradient g) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ (modelPolynomial g)) :=
    (contDiff_infty_iff_fderiv.mp (modelPolynomial_contDiff g)).2
  apply contDiff_pi.mpr
  intro i
  exact hd.clm_apply contDiff_const

theorem modelNormalEnergy_contDiff (g : ℕ) : ContDiff ℝ ∞ (modelNormalEnergy g) := by
  apply ContDiff.sum
  intro i _
  exact ((contDiff_apply ℝ ℝ i).comp (modelGradient_contDiff g)).pow 2

theorem model_linearMap_coordinate_sum (D : ModelAmbient →L[ℝ] ℝ) (v : ModelAmbient) :
    D v = ∑ i : Fin 3, v i * D (Pi.single i 1) := by
  have hv : v = ∑ i : Fin 3, v i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, map_smul, smul_eq_mul]

theorem modelGradient_pairing (g : ℕ) (p : ModelAmbient) :
    fderiv ℝ (modelPolynomial g) p (modelGradient g p) = modelNormalEnergy g p := by
  rw [model_linearMap_coordinate_sum]
  simp [modelGradient, modelNormalEnergy, pow_two]

theorem modelGradient_ne_zero (g : ℕ) (p : ModelAmbient)
    (hz : modelPolynomial g p = 0) : modelGradient g p ≠ 0 := by
  intro hzero
  apply modelPolynomial_regular g p hz
  apply ContinuousLinearMap.ext
  intro v
  rw [model_linearMap_coordinate_sum]
  have hcoeff (i : Fin 3) : fderiv ℝ (modelPolynomial g) p (Pi.single i 1) = 0 := by
    exact congrFun hzero i
  simp [hcoeff]

theorem modelNormalEnergy_pos (g : ℕ) (p : ModelAmbient)
    (hz : modelPolynomial g p = 0) : 0 < modelNormalEnergy g p := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, modelGradient g p i ≠ 0 := by
    by_contra h
    apply modelGradient_ne_zero g p hz
    ext i
    simpa using (not_exists.mp h i)
  exact Finset.sum_pos' (fun j _ => sq_nonneg (modelGradient g p j))
    ⟨i, mem_univ i, sq_pos_of_ne_zero hi⟩

theorem modelTransverseVector_pairing (g : ℕ) (p : ModelAmbient)
    (hz : modelPolynomial g p = 0) :
    fderiv ℝ (modelPolynomial g) p (modelTransverseVector g p) = 1 := by
  simp only [modelTransverseVector, map_smul, smul_eq_mul, modelGradient_pairing]
  exact inv_mul_cancel₀ (ne_of_gt (modelNormalEnergy_pos g p hz))

theorem modelTransverseVector_ne_zero (g : ℕ) (p : ModelAmbient)
    (hz : modelPolynomial g p = 0) : modelTransverseVector g p ≠ 0 := by
  intro hzero
  have h := modelTransverseVector_pairing g p hz
  rw [hzero, map_zero] at h
  exact zero_ne_one h

theorem modelTransverseVector_contDiffAt (g : ℕ) (p : ModelAmbient)
    (hz : modelPolynomial g p = 0) : ContDiffAt ℝ ∞ (modelTransverseVector g) p := by
  exact ((modelNormalEnergy_contDiff g).contDiffAt.inv
    (ne_of_gt (modelNormalEnergy_pos g p hz))).smul (modelGradient_contDiff g).contDiffAt

theorem model_kernel_remainder (g : ℕ) (p v : ModelAmbient)
    (hz : modelPolynomial g p = 0) :
    fderiv ℝ (modelPolynomial g) p
      (v - (fderiv ℝ (modelPolynomial g) p v) • modelTransverseVector g p) = 0 := by
  simp [map_sub, map_smul, modelTransverseVector_pairing g p hz]

theorem model_transverse_coefficient_unique (g : ℕ) (p w : ModelAmbient)
    (hz : modelPolynomial g p = 0) (hw : fderiv ℝ (modelPolynomial g) p w = 0)
    (t : ℝ) :
    fderiv ℝ (modelPolynomial g) p (w + t • modelTransverseVector g p) = t := by
  simp [map_add, map_smul, hw, modelTransverseVector_pairing g p hz]

def modelKernelLinearEquiv (g : ℕ) (p : ModelAmbient) (hz : modelPolynomial g p = 0) :
    ModelAmbient ≃ₗ[ℝ] (LinearMap.ker (fderiv ℝ (modelPolynomial g) p).toLinearMap) × ℝ where
  toFun := fun v => (⟨v - (fderiv ℝ (modelPolynomial g) p v) • modelTransverseVector g p,
    model_kernel_remainder g p v hz⟩, fderiv ℝ (modelPolynomial g) p v)
  invFun := fun q => q.1.val + q.2 • modelTransverseVector g p
  left_inv := by
    intro v
    exact sub_add_cancel v _
  right_inv := by
    rintro ⟨w, t⟩
    have hw : fderiv ℝ (modelPolynomial g) p w.val = 0 := w.property
    apply Prod.ext
    · apply Subtype.ext
      change w.val + t • modelTransverseVector g p -
        (fderiv ℝ (modelPolynomial g) p (w.val + t • modelTransverseVector g p)) •
          modelTransverseVector g p = w.val
      rw [model_transverse_coefficient_unique g p w.val hz hw t]
      exact add_sub_cancel_right _ _
    · exact model_transverse_coefficient_unique g p w.val hz hw t
  map_add' := by
    intro v w
    apply Prod.ext
    · apply Subtype.ext
      change v + w - (fderiv ℝ (modelPolynomial g) p (v + w)) • modelTransverseVector g p =
        (v - (fderiv ℝ (modelPolynomial g) p v) • modelTransverseVector g p) +
        (w - (fderiv ℝ (modelPolynomial g) p w) • modelTransverseVector g p)
      rw [map_add, add_smul]
      abel
    · exact map_add _ _ _
  map_smul' := by
    intro t v
    apply Prod.ext
    · apply Subtype.ext
      change t • v - (fderiv ℝ (modelPolynomial g) p (t • v)) • modelTransverseVector g p =
        t • (v - (fderiv ℝ (modelPolynomial g) p v) • modelTransverseVector g p)
      simp [map_smul, smul_sub, smul_smul]
    · exact map_smul _ _ _

def modelKernelSplit (g : ℕ) (p : ModelAmbient) (hz : modelPolynomial g p = 0) :
    ModelAmbient ≃L[ℝ] (LinearMap.ker (fderiv ℝ (modelPolynomial g) p).toLinearMap) × ℝ :=
  (modelKernelLinearEquiv g p hz).toContinuousLinearEquiv

theorem exists_modelKernelSplit (g : ℕ) (p : ModelAmbient)
    (hz : modelPolynomial g p = 0) :
    Nonempty (ModelAmbient ≃L[ℝ]
      (LinearMap.ker (fderiv ℝ (modelPolynomial g) p).toLinearMap) × ℝ) :=
  ⟨modelKernelSplit g p hz⟩

theorem modelKernel_finrank (g : ℕ) (p : ModelAmbient) (hz : modelPolynomial g p = 0) :
    Module.finrank ℝ (LinearMap.ker (fderiv ℝ (modelPolynomial g) p).toLinearMap) = 2 := by
  have h := (modelKernelLinearEquiv g p hz).finrank_eq
  rw [Module.finrank_prod] at h
  have ha : Module.finrank ℝ ModelAmbient = 3 := by simp [ModelAmbient]
  have hr : Module.finrank ℝ ℝ = 1 := by simp
  rw [ha, hr] at h
  omega

end R4Embedding
