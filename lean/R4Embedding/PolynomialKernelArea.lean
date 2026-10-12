import R4Embedding.PolynomialNormal
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Orientation

/-! The canonical nonzero area form of the actual polynomial derivative kernel.
Its sign is induced by the ambient determinant and the constructed transverse
vector. Chartwise local constancy, hence SurfaceOrientation, is still required.
-/

set_option autoImplicit false
noncomputable section
namespace R4Embedding

open Module

abbrev ModelDerivativeKernel (g : ℕ) (p : ModelAmbient) :=
  LinearMap.ker (fderiv ℝ (modelPolynomial g) p).toLinearMap

def modelNormalKernelEquiv (g : ℕ) (p : ModelAmbient) (hz : modelPolynomial g p = 0) :
    (ℝ × ModelDerivativeKernel g p) ≃ₗ[ℝ] ModelAmbient :=
  (LinearEquiv.prodComm ℝ ℝ (ModelDerivativeKernel g p)).trans
    (modelKernelLinearEquiv g p hz).symm

theorem modelNormalKernelEquiv_apply (g : ℕ) (p : ModelAmbient)
    (hz : modelPolynomial g p = 0) (t : ℝ) (w : ModelDerivativeKernel g p) :
    modelNormalKernelEquiv g p hz (t, w) = w.val + t • modelTransverseVector g p := rfl

def modelKernelBasis (g : ℕ) (p : ModelAmbient) (hz : modelPolynomial g p = 0) :
    Basis (Fin 2) ℝ (ModelDerivativeKernel g p) :=
  Module.finBasisOfFinrankEq ℝ (ModelDerivativeKernel g p) (modelKernel_finrank g p hz)

def modelNormalKernelBasis (g : ℕ) (p : ModelAmbient) (hz : modelPolynomial g p = 0) :
    Basis (Fin 3) ℝ ModelAmbient :=
  (((Basis.singleton (Fin 1) ℝ).prod (modelKernelBasis g p hz)).map
    (modelNormalKernelEquiv g p hz)).reindex finSumFinEquiv

theorem modelNormalKernelBasis_zero (g : ℕ) (p : ModelAmbient)
    (hz : modelPolynomial g p = 0) :
    modelNormalKernelBasis g p hz 0 = modelTransverseVector g p := by
  simp only [modelNormalKernelBasis, Basis.reindex_apply, Basis.map_apply]
  change modelNormalKernelEquiv g p hz
    (((Basis.singleton (Fin 1) ℝ).prod (modelKernelBasis g p hz)) (Sum.inl 0)) = _
  have hpair : ((Basis.singleton (Fin 1) ℝ).prod (modelKernelBasis g p hz)) (Sum.inl 0) =
      (1, 0) := by
    apply Prod.ext
    · simp [Basis.prod_apply_inl_fst]
    · exact Basis.prod_apply_inl_snd _ _ _
  rw [hpair, modelNormalKernelEquiv_apply]
  simp

theorem modelNormalKernelBasis_succ (g : ℕ) (p : ModelAmbient)
    (hz : modelPolynomial g p = 0) (j : Fin 2) :
    modelNormalKernelBasis g p hz j.succ = (modelKernelBasis g p hz j).val := by
  simp only [modelNormalKernelBasis, Basis.reindex_apply, Basis.map_apply]
  have hi : (finSumFinEquiv : Fin 1 ⊕ Fin 2 ≃ Fin 3) (Sum.inr j) = j.succ := by
    change Fin.natAdd 1 j = j.succ
    apply Fin.ext
    simp [Nat.add_comm]
  change modelNormalKernelEquiv g p hz
    (((Basis.singleton (Fin 1) ℝ).prod (modelKernelBasis g p hz))
      (finSumFinEquiv.symm j.succ)) = _
  rw [← hi, Equiv.symm_apply_apply]
  have hpair : ((Basis.singleton (Fin 1) ℝ).prod (modelKernelBasis g p hz)) (Sum.inr j) =
      (0, modelKernelBasis g p hz j) := by
    apply Prod.ext
    · exact Basis.prod_apply_inr_fst _ _ _
    · exact Basis.prod_apply_inr_snd _ _ _
  rw [hpair, modelNormalKernelEquiv_apply]
  simp

def modelKernelArea (g : ℕ) (p : ModelAmbient) :
    (ModelDerivativeKernel g p) [⋀^Fin 2]→ₗ[ℝ] ℝ :=
  (((Pi.basisFun ℝ (Fin 3)).det).curryLeft (modelTransverseVector g p)).compLinearMap
    (ModelDerivativeKernel g p).subtype

theorem modelKernelArea_on_basis (g : ℕ) (p : ModelAmbient)
    (hz : modelPolynomial g p = 0) :
    modelKernelArea g p (modelKernelBasis g p hz) =
      (Pi.basisFun ℝ (Fin 3)).det (modelNormalKernelBasis g p hz) := by
  change (Pi.basisFun ℝ (Fin 3)).det
    (Matrix.vecCons (modelTransverseVector g p) (fun j => (modelKernelBasis g p hz j).val)) = _
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using (modelNormalKernelBasis_zero g p hz).symm
  · simpa using (modelNormalKernelBasis_succ g p hz j).symm

theorem modelKernelArea_ne_zero (g : ℕ) (p : ModelAmbient)
    (hz : modelPolynomial g p = 0) : modelKernelArea g p ≠ 0 := by
  have hn : (Pi.basisFun ℝ (Fin 3)).det (modelNormalKernelBasis g p hz) ≠ 0 :=
    ((Pi.basisFun ℝ (Fin 3)).isUnit_det (modelNormalKernelBasis g p hz)).ne_zero
  intro hzero
  apply hn
  rw [← modelKernelArea_on_basis g p hz, hzero]
  rfl

def modelKernelOrientation (g : ℕ) (p : ModelAmbient) (hz : modelPolynomial g p = 0) :
    Orientation ℝ (ModelDerivativeKernel g p) (Fin 2) :=
  rayOfNeZero ℝ (modelKernelArea g p) (modelKernelArea_ne_zero g p hz)

theorem exists_modelKernelOrientation (g : ℕ) (p : ModelAmbient)
    (hz : modelPolynomial g p = 0) :
    Nonempty (Orientation ℝ (ModelDerivativeKernel g p) (Fin 2)) :=
  ⟨modelKernelOrientation g p hz⟩

end R4Embedding
