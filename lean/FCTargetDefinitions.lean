import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.Sheaf.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.LinearAlgebra.Orientation
import Mathlib.Topology.LocallyConstant.Basic

namespace SmoothIsometricEmbeddingR4

open scoped ContDiff Manifold

/-- An orientation of the tangent spaces that is locally constant in every chart. -/
def IsOrientableSurface (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ M] : Prop :=
  ∃ o : M → Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2),
    ∀ p : M, IsLocallyConstant (fun x : (chartAt (EuclideanSpace ℝ (Fin 2)) p).source =>
      let D : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
          (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p) x.val
      Orientation.map (Fin 2)
        (D.toLinearMap.linearEquivOfInjective
          (isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
            (by simpa only [extChartAt_source] using x.property)).injective rfl)
        (o x.val))


end SmoothIsometricEmbeddingR4
