import R4Embedding.PolynomialDouble
import R4Embedding.InitialEmbeddingTransport
import Mathlib.Topology.Algebra.ConstMulAction

/-! The zero-parameter polynomial level is the standard unit two-sphere
by an explicit linear rescaling. This proves a topological identification
of this concrete model, not smooth classification of a supplied atlas. -/

set_option autoImplicit false
noncomputable section
namespace R4Embedding

open Manifold
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem modelPolynomial_zero_formula (p : ModelAmbient) :
    modelPolynomial 0 p = (p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 - 9 := by
  simp [modelPolynomial, modelFactor, modelCircleFactor, modelRadius]
  ring

theorem rawModelAmbientToThree_norm_sq (p : ModelAmbient) :
    ‖rawModelAmbientToThree p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 := by
  simpa [rawModelAmbientToThree, Fin.sum_univ_three] using
    EuclideanSpace.real_norm_sq_eq (rawModelAmbientToThree p)

theorem modelPolynomial_zero_iff_norm (p : ModelAmbient) :
    modelPolynomial 0 p = 0 ↔ ‖rawModelAmbientToThree p‖ = 3 := by
  rw [modelPolynomial_zero_formula]
  have hs := rawModelAmbientToThree_norm_sq p
  have hn := norm_nonneg (rawModelAmbientToThree p)
  constructor <;> intro h <;> nlinarith

def modelZeroAmbientHomeomorph : ModelAmbient ≃ₜ ThreeSpace :=
  rawModelAmbientToThree.toHomeomorph.trans
    (Homeomorph.smulOfNeZero (1 / 3 : ℝ) (by norm_num))

theorem modelZeroAmbientHomeomorph_apply (p : ModelAmbient) :
    modelZeroAmbientHomeomorph p = (1 / 3 : ℝ) • rawModelAmbientToThree p := rfl

theorem modelZeroAmbientHomeomorph_symm_apply (u : ThreeSpace) :
    modelZeroAmbientHomeomorph.symm u = rawModelAmbientToThree.symm ((3 : ℝ) • u) := by
  simp [modelZeroAmbientHomeomorph]

theorem modelPolynomial_zero_iff_unit_sphere (p : ModelAmbient) :
    modelPolynomial 0 p = 0 ↔ modelZeroAmbientHomeomorph p ∈ UnitTwoSphere := by
  rw [modelPolynomial_zero_iff_norm]
  change _ ↔ modelZeroAmbientHomeomorph p ∈ Metric.sphere (0 : ThreeSpace) 1
  simp only [Metric.mem_sphere, dist_zero_right, modelZeroAmbientHomeomorph_apply,
    norm_smul, Real.norm_eq_abs]
  norm_num
  constructor <;> intro h <;> linarith

def polynomialZeroSphereHomeomorph : PolynomialLevel 0 ≃ₜ UnitTwoSphere :=
  modelZeroAmbientHomeomorph.subtype modelPolynomial_zero_iff_unit_sphere

theorem polynomialZeroSphereHomeomorph_apply (p : PolynomialLevel 0) :
    (polynomialZeroSphereHomeomorph p : ThreeSpace) =
      (1 / 3 : ℝ) • rawModelAmbientToThree p.val := rfl

theorem polynomialZeroSphereHomeomorph_symm_apply (u : UnitTwoSphere) :
    (polynomialZeroSphereHomeomorph.symm u).val =
      rawModelAmbientToThree.symm ((3 : ℝ) • u.val) := by
  exact modelZeroAmbientHomeomorph_symm_apply u.val

theorem exists_polynomialZeroSphereHomeomorph :
    Nonempty (PolynomialLevel 0 ≃ₜ UnitTwoSphere) :=
  ⟨polynomialZeroSphereHomeomorph⟩

def modelDoubleZeroSphereHomeomorph : ModelDouble 0 ≃ₜ UnitTwoSphere :=
  (modelDoubleHomeomorph 0).trans polynomialZeroSphereHomeomorph

theorem exists_modelDoubleZeroSphereHomeomorph :
    Nonempty (ModelDouble 0 ≃ₜ UnitTwoSphere) :=
  ⟨modelDoubleZeroSphereHomeomorph⟩

theorem polynomialZeroSphereHomeomorph_contMDiff :
    let _ := polynomialLevelChartedSpace 0
    ContMDiff planeModel planeModel ∞ polynomialZeroSphereHomeomorph := by
  let _ := polynomialLevelChartedSpace 0
  let _ := polynomialLevel_isManifold 0
  have hi : ContMDiff planeModel threeModel ∞
      (rawModelAmbientToThree ∘ (Subtype.val : PolynomialLevel 0 → ModelAmbient)) := by
    let _ := polynomialLevelRawChartedSpace 0
    let _ := polynomialLevelRaw_isManifold 0
    exact (initialThreeEmbedding_of_raw_model
      (polynomialLevelRaw_inclusion_contMDiff 0) Subtype.val_injective
      (polynomialLevelRaw_inclusion_mfderiv_injective 0)).1
  have hscale : ContMDiff threeModel threeModel ∞
      (fun u : ThreeSpace => (1 / 3 : ℝ) • u) :=
    ((1 / 3 : ℝ) • ContinuousLinearMap.id ℝ ThreeSpace).contDiff.contMDiff
  exact (hscale.comp hi).codRestrict_sphere
    (fun p => (polynomialZeroSphereHomeomorph p).property)

theorem polynomialZeroSphereHomeomorph_symm_contMDiff :
    let _ := polynomialLevelChartedSpace 0
    ContMDiff planeModel planeModel ∞ polynomialZeroSphereHomeomorph.symm := by
  let _ := polynomialLevelRawChartedSpace 0
  let _ := polynomialLevelRaw_isManifold 0
  let F : UnitTwoSphere → ModelAmbient :=
    fun u => rawModelAmbientToThree.symm ((3 : ℝ) • u.val)
  have hF : ContMDiff planeModel 𝓘(ℝ, ModelAmbient) ∞ F :=
    rawModelAmbientToThree.symm.contDiff.contMDiff.comp
      (((3 : ℝ) • ContinuousLinearMap.id ℝ ThreeSpace).contDiff.contMDiff.comp
        contMDiff_coe_sphere)
  have hzero : ∀ u, modelPolynomial 0 (F u) = 0 := by
    intro u
    change modelPolynomial 0
      (rawModelAmbientToThree.symm ((3 : ℝ) • u.val)) = 0
    rw [← polynomialZeroSphereHomeomorph_symm_apply]
    exact (polynomialZeroSphereHomeomorph.symm u).property
  have hraw := R4ModelAtlas.RegularLevel.contMDiff_level_factor (m := 2)
    𝓘(ℝ, ModelAmbient) (modelPolynomial_contMDiff 0)
    (modelPolynomial_mfderiv_ne_zero 0) hF hzero
  apply (contMDiff_chartedSpaceTransHomeomorph_iff
    𝓘(ℝ, RawModelPlane) planeModel rawModelPlaneToPlane.toHomeomorph
    rawModelPlaneToPlane (fun _ => rfl) planeModel).mpr
  convert hraw using 1
  funext u
  apply Subtype.ext
  exact polynomialZeroSphereHomeomorph_symm_apply u

def polynomialZeroSphereDiffeomorph :
    let _ := polynomialLevelChartedSpace 0
    Diffeomorph planeModel planeModel (PolynomialLevel 0) UnitTwoSphere ∞ := by
  let _ := polynomialLevelChartedSpace 0
  exact { polynomialZeroSphereHomeomorph with
    contMDiff_toFun := polynomialZeroSphereHomeomorph_contMDiff
    contMDiff_invFun := polynomialZeroSphereHomeomorph_symm_contMDiff }

theorem exists_polynomialZeroSphereDiffeomorph :
    let _ := polynomialLevelChartedSpace 0
    Nonempty (Diffeomorph planeModel planeModel (PolynomialLevel 0) UnitTwoSphere ∞) :=
  ⟨polynomialZeroSphereDiffeomorph⟩

end R4Embedding
