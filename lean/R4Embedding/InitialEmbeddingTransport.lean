import R4Embedding.SphericalTransfer
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! Concrete initial models and transport through an actual smooth
diffeomorphism. These results do not assert smooth classification of every
closed orientable surface or existence of a model for every genus. -/

noncomputable section
namespace R4Embedding

open Manifold
open scoped ContDiff

universe u v
variable {M : Type u} {N : Type v}
  [TopologicalSpace M] [ChartedSpace Plane M]
  [TopologicalSpace N] [ChartedSpace Plane N]

theorem initialThreeEmbedding_comp_diffeomorph
    (e : Diffeomorph planeModel planeModel M N ∞) {f : N → ThreeSpace}
    (hs : ContMDiff planeModel threeModel ∞ f) (hi : Function.Injective f)
    (hm : ∀ p, Function.Injective (mfderiv planeModel threeModel f p)) :
    ContMDiff planeModel threeModel ∞ (f ∘ e) ∧ Function.Injective (f ∘ e) ∧
      ∀ p, Function.Injective (mfderiv planeModel threeModel (f ∘ e) p) := by
  refine ⟨hs.comp e.contMDiff, hi.comp e.injective, ?_⟩
  intro p
  rw [mfderiv_comp p ((hs (e p)).mdifferentiableAt (by simp))
    (e.contMDiffAt.mdifferentiableAt (by simp))]
  exact (hm (e p)).comp ((e.isInvertible_mfderiv (x := p) (by simp)).injective)

theorem exists_initial_three_embedding_of_diffeomorph
    (e : Diffeomorph planeModel planeModel M N ∞)
    (hN : ∃ f : N → ThreeSpace, ContMDiff planeModel threeModel ∞ f ∧
      Function.Injective f ∧ ∀ p, Function.Injective (mfderiv planeModel threeModel f p)) :
    ∃ f : M → ThreeSpace, ContMDiff planeModel threeModel ∞ f ∧
      Function.Injective f ∧ ∀ p, Function.Injective (mfderiv planeModel threeModel f p) := by
  obtain ⟨f, hs, hi, hm⟩ := hN
  exact ⟨f ∘ e, initialThreeEmbedding_comp_diffeomorph e hs hi hm⟩

abbrev UnitTwoSphere := Metric.sphere (0 : ThreeSpace) 1

local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem unitTwoSphere_initial_three_embedding :
    ∃ f : UnitTwoSphere → ThreeSpace, ContMDiff planeModel threeModel ∞ f ∧
      Function.Injective f ∧ ∀ p, Function.Injective (mfderiv planeModel threeModel f p) := by
  refine ⟨Subtype.val, contMDiff_coe_sphere, Subtype.val_injective, ?_⟩
  intro p u v huv
  apply injective_mvfderiv_subtypeVal_sphere p
  exact congrArg (NormedSpace.fromTangentSpace _) huv

theorem exists_initial_three_embedding_of_sphere_diffeomorph
    (e : Diffeomorph planeModel planeModel M UnitTwoSphere ∞) :
    ∃ f : M → ThreeSpace, ContMDiff planeModel threeModel ∞ f ∧
      Function.Injective f ∧ ∀ p, Function.Injective (mfderiv planeModel threeModel f p) :=
  exists_initial_three_embedding_of_diffeomorph e unitTwoSphere_initial_three_embedding

end R4Embedding
