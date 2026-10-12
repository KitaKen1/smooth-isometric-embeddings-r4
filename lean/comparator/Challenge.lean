import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.LinearAlgebra.Orientation
import Mathlib.Topology.LocallyConstant.Basic

/-! Comparator challenge (stage 11): the complete target, stated from Mathlib alone.

Every closed orientable smooth surface `M` (compact, Hausdorff, modelled on the plane without
boundary, with its own smooth atlas; empty and disconnected surfaces included) and every smooth
Riemannian metric `g` on it admit a smooth map `F : M → ℝ⁴` that is injective and preserves the
inner product of tangent vectors. Orientability is a locally constant tangent orientation read in
the actual charts; no embedding is assumed.

Each definition below is copied verbatim (same names, binders, variables and `open`s) from the
main line, where the theorem is proved:
- `R4Embedding/Problem.lean`: `Plane`, `Space`, `planeModel`, `spaceModel`, `SmoothMetric`,
  `euclideanDerivative`, `IsSmoothIsometricMap`, `IsSmoothIsometricEmbedding`;
- `R4Embedding/SurfaceOrientation.lean`: `preferredSurfaceChartEquiv`, `SurfaceOrientation`,
  `IsOrientableSurface`;
- `R4Embedding/MainStatement.lean`: `ClosedOrientableSurfaceEmbeddingStatement`.
Comparator requires every declaration the statement uses to be identical in the solution
environment; `comparator/check_challenge.py` checks this locally beforehand (structural equality
after renaming the namespace). The solution module is `R4Initial.FinalTheorem`. -/

noncomputable section

namespace R4Embedding

section Problem

open Bundle Manifold
open scoped ContDiff

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Space := EuclideanSpace ℝ (Fin 4)
abbrev planeModel := 𝓘(ℝ, Plane)
abbrev spaceModel := 𝓘(ℝ, Space)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

/-- A smooth positive-definite metric on the tangent bundle of a surface. -/
abbrev SmoothMetric (M : Type*) [TopologicalSpace M] [ChartedSpace Plane M]
    [IsManifold planeModel ∞ M] :=
  Bundle.ContMDiffRiemannianMetric planeModel ∞ Plane
    (fun p : M => TangentSpace planeModel p)

/-- The canonical identification of the target tangent space with Euclidean
four-space makes its inner product explicit. -/
def euclideanDerivative (f : M → Space) (p : M) :
    TangentSpace planeModel p →L[ℝ] Space :=
  (NormedSpace.fromTangentSpace (f p)).toContinuousLinearMap.comp
    (mfderiv planeModel spaceModel f p)

/-- The analytic property required of the construction. -/
def IsSmoothIsometricMap (g : SmoothMetric M) (f : M → Space) : Prop :=
  ContMDiff planeModel spaceModel ∞ f ∧
    ∀ (p : M) (v w : TangentSpace planeModel p),
      inner ℝ (euclideanDerivative f p v) (euclideanDerivative f p w) = g.inner p v w

/-- On a compact surface, injectivity gives the topological embedding part.
The positive metric also forces an injective tangent derivative. -/
def IsSmoothIsometricEmbedding (g : SmoothMetric M) (f : M → Space) : Prop :=
  IsSmoothIsometricMap g f ∧ Function.Injective f

end Problem

section SurfaceOrientation

open Set Function Manifold TopologicalSpace
open scoped Manifold ContDiff Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

variable [IsManifold planeModel ∞ M]

def preferredSurfaceChartEquiv (p x : M) (hx : x ∈ (chartAt Plane p).source) :
    Plane ≃L[ℝ] Plane := by
  let D : Plane →L[ℝ] Plane := mfderiv planeModel planeModel (extChartAt planeModel p) x
  have hi : Injective D :=
    (isInvertible_mfderiv_extChartAt (I := planeModel)
      (by simpa only [extChartAt_source] using hx)).injective
  exact (D.toLinearMap.linearEquivOfInjective hi rfl).toContinuousLinearEquiv

/-- A tangent orientation locally constant when read in each actual chart.
Its existence is independent of any initial embedding. -/
def SurfaceOrientation (M : Type*) [TopologicalSpace M] [ChartedSpace Plane M]
    [IsManifold planeModel ∞ M] : Type _ :=
  {o : M → Orientation ℝ Plane (Fin 2) //
    ∀ p : M, IsLocallyConstant (fun x : (chartAt Plane p).source =>
      Orientation.map (Fin 2)
        (preferredSurfaceChartEquiv p x.val x.property).toLinearEquiv (o x.val))}

def IsOrientableSurface (M : Type*) [TopologicalSpace M] [ChartedSpace Plane M]
    [IsManifold planeModel ∞ M] : Prop := Nonempty (SurfaceOrientation M)

end SurfaceOrientation

section MainStatement

open Manifold TopologicalSpace
open scoped ContDiff
universe u

/-- Closed means compact and Hausdorff; the plane model has no boundary.
Empty and disconnected surfaces are included, with every smooth metric. -/
def ClosedOrientableSurfaceEmbeddingStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace Plane M]
    [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M],
    IsOrientableSurface M → ∀ g : SmoothMetric M,
      ∃ F : M → Space, IsSmoothIsometricEmbedding g F

/-- Every closed orientable smooth Riemannian surface embeds isometrically and smoothly in `ℝ⁴`. -/
theorem closedOrientableSurfaceEmbedding : ClosedOrientableSurfaceEmbeddingStatement.{u} := by
  sorry

end MainStatement

end R4Embedding
