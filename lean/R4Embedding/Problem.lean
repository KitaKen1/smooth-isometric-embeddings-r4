import R4Embedding.ChartEmbedding
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-! The metric in this specification is a standard smooth Riemannian metric.
Isometric means preservation of tangent inner products, not preservation of
ambient chord distance. Existence for every orientable surface remains a
separate, unproved task; no orientability surrogate is introduced here. -/

noncomputable section

namespace R4Embedding

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

theorem IsSmoothIsometricMap.mfderiv_injective
    {g : SmoothMetric M} {f : M → Space} (hf : IsSmoothIsometricMap g f) (p : M) :
    Function.Injective (mfderiv planeModel spaceModel f p) := by
  intro v w heq
  by_contra hne
  have heq' : euclideanDerivative f p v = euclideanDerivative f p w :=
    congrArg (NormedSpace.fromTangentSpace (f p)) heq
  have hzero : euclideanDerivative f p (v - w) = 0 := by
    rw [map_sub, heq', sub_self]
  have hmetric := hf.2 p (v - w) (v - w)
  rw [hzero, inner_zero_left] at hmetric
  have hpos := g.pos p (v - w) (sub_ne_zero.mpr hne)
  exact (ne_of_gt hpos) hmetric.symm

theorem IsSmoothIsometricEmbedding.isClosedEmbedding [CompactSpace M]
    {g : SmoothMetric M} {f : M → Space} (hf : IsSmoothIsometricEmbedding g f) :
    Topology.IsClosedEmbedding f :=
  hf.1.1.continuous.isClosedEmbedding hf.2

/-- This is the remaining construction contract: the *same* metric-preserving
map must satisfy every chart certificate and the C⁰ bound. These hypotheses
are explicit inputs, not axioms or a claimed solution of the surface theorem. -/
theorem exists_isometric_embedding_of_certified_construction [CompactSpace M]
    (g : SmoothMetric M) {ι : Type*} (patch : ι → Set M)
    (hopen : ∀ i, IsOpen (patch i)) (hcover : ∀ p, ∃ i, p ∈ patch i)
    {F : M → Space} (hF : Continuous F) (hFinj : Function.Injective F)
    (hconstruct : ∀ ε : ℝ, 0 < ε → ∃ f : M → Space,
      IsSmoothIsometricMap g f ∧
      (∀ i, Nonempty (ProjectedChartCertificate (E := Plane) (patch i) f)) ∧
      (∀ p, dist (f p) (F p) < ε)) :
    ∃ f : M → Space, IsSmoothIsometricEmbedding g f := by
  obtain ⟨ε, hε, htol⟩ := exists_embedding_tolerance_of_projected_charts
    (E := Plane) patch hopen hcover hF hFinj
  obtain ⟨f, hmetric, hcert, hclose⟩ := hconstruct ε hε
  exact ⟨f, hmetric, (htol f hmetric.1.continuous hcert hclose).injective⟩

end R4Embedding
