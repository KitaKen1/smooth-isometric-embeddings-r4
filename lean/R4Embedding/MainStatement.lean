import R4Embedding.OpenMetric
import R4Embedding.SurfaceOrientation

/-! The complete target has no initial embedding hypothesis. These reductions
retain the missing connected initial-existence or analytic theorem as explicit
inputs; they do not assert either missing construction. -/

noncomputable section
namespace R4Embedding

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

def ConnectedClosedOrientableSurfaceEmbeddingStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace Plane M]
    [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] [ConnectedSpace M],
    IsOrientableSurface M → ∀ g : SmoothMetric M,
      ∃ F : M → Space, IsSmoothIsometricEmbedding g F

def ConnectedInitialThreeEmbeddingStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace Plane M]
    [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] [ConnectedSpace M],
    IsOrientableSurface M → ∃ f : M → ThreeSpace,
      ContMDiff planeModel threeModel ∞ f ∧ Function.Injective f ∧
      ∀ p, Function.Injective (mfderiv planeModel threeModel f p)

def InitialThreeEmbeddingStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace Plane M]
    [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M],
    IsOrientableSurface M → ∃ f : M → ThreeSpace,
      ContMDiff planeModel threeModel ∞ f ∧ Function.Injective f ∧
      ∀ p, Function.Injective (mfderiv planeModel threeModel f p)

/-- The actual analytic entry has no connectedness or orientation input;
its initial three-space embedding input is still explicit. -/
def IsometricEmbeddingFromThreeStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace Plane M]
    [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
    (g : SmoothMetric M) (f : M → ThreeSpace),
    ContMDiff planeModel threeModel ∞ f → Function.Injective f →
    (∀ p, Function.Injective (mfderiv planeModel threeModel f p)) →
      ∃ F : M → Space, IsSmoothIsometricEmbedding g F

theorem closed_statement_of_connected_statement
    (hconnected : ConnectedClosedOrientableSurfaceEmbeddingStatement.{u}) :
    ClosedOrientableSurfaceEmbeddingStatement.{u} := by
  intro M _ _ _ _ _ horient g
  apply exists_isometric_embedding_of_component_embeddings g
  intro c
  exact hconnected (componentOpen c) (isOrientableSurface_component c horient)
    (restrictSmoothMetric (componentOpen c) g)

theorem initial_three_statement_of_connected_statement
    (hconnected : ConnectedInitialThreeEmbeddingStatement.{u}) :
    InitialThreeEmbeddingStatement.{u} := by
  intro M _ _ _ _ _ horient
  apply exists_three_embedding_of_component_embeddings
  intro c
  exact hconnected (componentOpen c) (isOrientableSurface_component c horient)

theorem closed_statement_of_connected_initial_and_analytic
    (hinitial : ConnectedInitialThreeEmbeddingStatement.{u})
    (hanalytic : IsometricEmbeddingFromThreeStatement.{u}) :
    ClosedOrientableSurfaceEmbeddingStatement.{u} := by
  intro M _ _ _ _ _ horient g
  obtain ⟨f, hs, hi, hm⟩ := initial_three_statement_of_connected_statement hinitial M horient
  exact hanalytic M g f hs hi hm

end R4Embedding
