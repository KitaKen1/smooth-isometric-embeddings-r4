import R4Embedding.PolynomialTangent
import R4Embedding.ImmersionAreaContinuity

/-! Actual chart-coherent orientation of every constructed polynomial level.
This does not identify its genus or classify an arbitrary supplied surface.
-/
set_option autoImplicit false
noncomputable section
namespace R4Embedding
open Manifold Module
open scoped Manifold ContDiff

local instance polynomialOrientationCharts (g : ℕ) : ChartedSpace Plane (PolynomialLevel g) :=
  polynomialLevelChartedSpace g
local instance polynomialOrientationManifold (g : ℕ) : IsManifold planeModel ∞ (PolynomialLevel g) :=
  polynomialLevel_isManifold g

theorem polynomialSurfaceArea_eq_immersion (g : ℕ) (p : PolynomialLevel g) :
    polynomialSurfaceArea g p = immersionSurfaceArea
      (Subtype.val : PolynomialLevel g → ModelAmbient)
      (fun q : PolynomialLevel g => modelTransverseVector g q.val) p := by
  apply AlternatingMap.ext
  intro v
  rfl

theorem polynomialLevel_isOrientable (g : ℕ) :
    let _ := polynomialLevelChartedSpace g
    let _ := polynomialLevel_isManifold g
    IsOrientableSurface (PolynomialLevel g) := by
  exact isOrientableSurface_of_forms
    ((Pi.basisFun ℝ (Fin 2)).map rawModelPlaneToPlane.toLinearEquiv)
    (polynomialSurfaceArea g) (polynomialSurfaceArea_ne_zero g) (fun p => by
      have h := immersionSurfaceChartArea_continuous (polynomialLevel_inclusion_contMDiff g)
        (polynomialLevel_transverse_continuous g) p
        ((Pi.basisFun ℝ (Fin 2)).map rawModelPlaneToPlane.toLinearEquiv)
      have he : polynomialSurfaceArea g = immersionSurfaceArea
          (Subtype.val : PolynomialLevel g → ModelAmbient)
          (fun q : PolynomialLevel g => modelTransverseVector g q.val) :=
        funext (polynomialSurfaceArea_eq_immersion g)
      simpa only [he] using h)

end R4Embedding
