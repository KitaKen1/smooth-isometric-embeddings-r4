import R4Embedding.PolynomialLevelAtlas
import R4Embedding.PolynomialKernelArea
import R4Embedding.ReducedLevelTangent
import R4Embedding.OrientationContinuity

/-! Actual tangent-kernel identification and area forms on the constructed
polynomial smooth surfaces. Chartwise continuity is a separate obligation.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace R4Embedding
open Manifold Module
open scoped Manifold ContDiff Topology

local instance polynomialPlaneCharts (g : ℕ) : ChartedSpace Plane (PolynomialLevel g) :=
  polynomialLevelChartedSpace g
local instance polynomialPlaneManifold (g : ℕ) : IsManifold planeModel ∞ (PolynomialLevel g) :=
  polynomialLevel_isManifold g

theorem polynomialLevel_inclusion_contMDiff (g : ℕ) :
    ContMDiff planeModel 𝓘(ℝ, ModelAmbient) ∞
      (Subtype.val : PolynomialLevel g → ModelAmbient) := by
  let _ := polynomialLevelRawChartedSpace g
  exact contMDiff_of_linear_model_change rawModelPlaneToPlane 𝓘(ℝ, ModelAmbient)
    (polynomialLevelRaw_inclusion_contMDiff g)

theorem polynomialLevel_inclusion_mfderiv_injective (g : ℕ) (p : PolynomialLevel g) :
    Function.Injective (mfderiv planeModel 𝓘(ℝ, ModelAmbient)
      (Subtype.val : PolynomialLevel g → ModelAmbient) p) := by
  let _ := polynomialLevelRawChartedSpace g
  exact mfderiv_injective_of_linear_model_change rawModelPlaneToPlane 𝓘(ℝ, ModelAmbient)
    (polynomialLevelRaw_inclusion_contMDiff g)
    (polynomialLevelRaw_inclusion_mfderiv_injective g) p

theorem polynomialLevelRaw_tangent_range (g : ℕ) :
    let _ := polynomialLevelRawChartedSpace g
    ∀ p : PolynomialLevel g,
      (mfderiv 𝓘(ℝ, RawModelPlane) 𝓘(ℝ, ModelAmbient) Subtype.val p).range =
        ModelDerivativeKernel g p.val := by
  let _ := polynomialLevelRawChartedSpace g
  dsimp only []
  have h := range_mfderiv_level_inclusion (m := 2) 𝓘(ℝ, ModelAmbient)
    (modelPolynomial_contMDiff g) (modelPolynomial_mfderiv_ne_zero g)
  intro p
  simpa only [mfderiv_eq_fderiv, ModelDerivativeKernel, TangentSpace] using h p

set_option backward.isDefEq.respectTransparency false in
theorem polynomialLevel_tangent_range (g : ℕ) (p : PolynomialLevel g) :
    (mfderiv planeModel 𝓘(ℝ, ModelAmbient) Subtype.val p).range =
      ModelDerivativeKernel g p.val := by
  let _ := polynomialLevelRawChartedSpace g
  rw [mfderiv_of_linear_model_change rawModelPlaneToPlane 𝓘(ℝ, ModelAmbient)
    (polynomialLevelRaw_inclusion_contMDiff g) p]
  rw [← polynomialLevelRaw_tangent_range g p]
  apply le_antisymm
  · rintro v ⟨w, rfl⟩
    exact ⟨rawModelPlaneToPlane.symm w, rfl⟩
  · rintro v ⟨w, rfl⟩
    refine ⟨rawModelPlaneToPlane w, ?_⟩
    change mfderiv 𝓘(ℝ, RawModelPlane) 𝓘(ℝ, ModelAmbient) Subtype.val p
      (rawModelPlaneToPlane.symm (rawModelPlaneToPlane w)) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
    rfl

def polynomialTangentKernelEquiv (g : ℕ) (p : PolynomialLevel g) :
    Plane ≃ₗ[ℝ] ModelDerivativeKernel g p.val :=
  (LinearEquiv.ofInjective
    (mfderiv planeModel 𝓘(ℝ, ModelAmbient) Subtype.val p).toLinearMap
    (polynomialLevel_inclusion_mfderiv_injective g p)).trans
    (LinearEquiv.ofEq _ _ (polynomialLevel_tangent_range g p))

def polynomialSurfaceArea (g : ℕ) (p : PolynomialLevel g) :
    Plane [⋀^Fin 2]→ₗ[ℝ] ℝ :=
  (modelKernelArea g p.val).compLinearMap
    (polynomialTangentKernelEquiv g p).toLinearMap

theorem polynomialTangentKernelEquiv_val (g : ℕ) (p : PolynomialLevel g) (v : Plane) :
    (polynomialTangentKernelEquiv g p v).val =
      mfderiv planeModel 𝓘(ℝ, ModelAmbient) Subtype.val p v := rfl

theorem polynomialSurfaceArea_apply (g : ℕ) (p : PolynomialLevel g) (v : Fin 2 → Plane) :
    polynomialSurfaceArea g p v = (Pi.basisFun ℝ (Fin 3)).det
      (Matrix.vecCons (modelTransverseVector g p.val)
        (fun i => mfderiv planeModel 𝓘(ℝ, ModelAmbient) Subtype.val p (v i))) := rfl

theorem polynomialSurfaceArea_ne_zero (g : ℕ) (p : PolynomialLevel g) :
    polynomialSurfaceArea g p ≠ 0 :=
  mt ((modelKernelArea g p.val).compLinearEquiv_eq_zero_iff
    (polynomialTangentKernelEquiv g p)).mp (modelKernelArea_ne_zero g p.val p.property)

theorem polynomialLevel_transverse_continuous (g : ℕ) :
    Continuous (fun p : PolynomialLevel g => modelTransverseVector g p.val) := by
  rw [continuous_iff_continuousAt]
  intro p
  exact ((modelTransverseVector_contDiffAt g p.val p.property).continuousAt).comp
    continuous_subtype_val.continuousAt

end R4Embedding
