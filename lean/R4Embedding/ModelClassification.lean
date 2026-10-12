import R4Embedding.MainStatement
import R4Embedding.InitialEmbeddingTransport
import R4Embedding.PolynomialLevelAtlas

/-! The remaining initial-embedding input, stated as smooth classification into
the explicit polynomial models. Each `PolynomialLevel g` already has a verified
initial three-space embedding in its actual atlas, so a diffeomorphism from the
supplied atlas suffices. The classification itself is an explicit input here;
it is not asserted. -/

noncomputable section
namespace R4Embedding

open Manifold
open scoped ContDiff
universe u

/-- Every closed connected orientable smooth surface is diffeomorphic, in its
supplied atlas, to one of the explicit polynomial level surfaces. -/
def PolynomialModelClassificationStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace Plane M]
    [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] [ConnectedSpace M],
    IsOrientableSurface M → ∃ g : ℕ,
      let _ := polynomialLevelChartedSpace g
      Nonempty (Diffeomorph planeModel planeModel M (PolynomialLevel g) ∞)

theorem connected_initial_of_polynomial_classification
    (hclass : PolynomialModelClassificationStatement.{u}) :
    ConnectedInitialThreeEmbeddingStatement.{u} := by
  intro M _ _ _ _ _ _ horient
  obtain ⟨g, hg⟩ := hclass M horient
  let _ := polynomialLevelChartedSpace g
  obtain ⟨e⟩ := hg
  exact exists_initial_three_embedding_of_diffeomorph e (polynomialLevel_initial_three_embedding g)

/-- The complete target from the two remaining inputs: smooth classification
into the explicit models and the analytic construction from a three-space embedding. -/
theorem closed_statement_of_polynomial_classification_and_analytic
    (hclass : PolynomialModelClassificationStatement.{u})
    (hanalytic : IsometricEmbeddingFromThreeStatement.{u}) :
    ClosedOrientableSurfaceEmbeddingStatement.{u} :=
  closed_statement_of_connected_initial_and_analytic
    (connected_initial_of_polynomial_classification hclass) hanalytic

/-- Topological classification into the explicit models: every closed connected
orientable smooth surface is homeomorphic to some `PolynomialLevel g`. This combines
the topological classification, the exclusion of non-orientable normal forms by the
smooth orientation, and the genus identification of the models. -/
def PolynomialTopologicalClassificationStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace Plane M]
    [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] [ConnectedSpace M],
    IsOrientableSurface M → ∃ g : ℕ, Nonempty (M ≃ₜ PolynomialLevel g)

/-- Two-dimensional smoothing: a homeomorphism from a closed smooth surface onto a
model surface can be replaced by a smooth diffeomorphism of the supplied atlases. -/
def PolynomialModelSmoothingStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace Plane M]
    [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] (g : ℕ),
    (M ≃ₜ PolynomialLevel g) →
      let _ := polynomialLevelChartedSpace g
      Nonempty (Diffeomorph planeModel planeModel M (PolynomialLevel g) ∞)

theorem polynomial_classification_of_topological_and_smoothing
    (htop : PolynomialTopologicalClassificationStatement.{u})
    (hsmooth : PolynomialModelSmoothingStatement.{u}) :
    PolynomialModelClassificationStatement.{u} := by
  intro M _ _ _ _ _ _ horient
  obtain ⟨g, ⟨h⟩⟩ := htop M horient
  exact ⟨g, hsmooth M g h⟩

end R4Embedding
