import R4Embedding.Problem
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! Transfer an existing smooth embedding in Euclidean three-space to the
unit sphere in four-space. This does not assert that every orientable surface
already has the required initial embedding. -/

noncomputable section
namespace R4Embedding

open Manifold
open scoped ContDiff

abbrev ThreeSpace := EuclideanSpace ℝ (Fin 3)
abbrev threeModel := 𝓘(ℝ, ThreeSpace)
abbrev UnitSphere := Metric.sphere (0 : Space) 1

local instance : Fact (Module.finrank ℝ Space = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

def sphericalPole : UnitSphere :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

def sphericalLift (pole : UnitSphere) {M : Type*} (f : M → ThreeSpace) : M → Space :=
  Subtype.val ∘ (stereographic' 3 pole).symm ∘ f

theorem stereographic_inverse_contMDiff (pole : UnitSphere) :
    ContMDiff threeModel (𝓡 3) ∞ (stereographic' 3 pole).symm := by
  have ha : stereographic' 3 pole ∈ atlas ThreeSpace UnitSphere := ⟨pole, rfl⟩
  have hs := contMDiffOn_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := 𝓡 3) (n := ∞) ha)
  exact contMDiffOn_univ.mp (by simpa using hs)

theorem stereographic_inverse_injective (pole : UnitSphere) :
    Function.Injective (stereographic' 3 pole).symm := by
  intro x y h
  exact (stereographic' 3 pole).symm.injOn (by simp) (by simp) h

theorem stereographic_inverse_mfderiv_injective (pole : UnitSphere) (x : ThreeSpace) :
    Function.Injective (mfderiv threeModel (𝓡 3) (stereographic' 3 pole).symm x) := by
  have ha : stereographic' 3 pole ∈ atlas ThreeSpace UnitSphere := ⟨pole, rfl⟩
  exact (mdifferentiable_of_mem_atlas (I := 𝓡 3) ha).symm.mfderiv_injective (by simp)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem sphericalLift_contMDiff (pole : UnitSphere) {f : M → ThreeSpace}
    (hf : ContMDiff planeModel threeModel ∞ f) :
    ContMDiff planeModel spaceModel ∞ (sphericalLift pole f) :=
  contMDiff_coe_sphere.comp ((stereographic_inverse_contMDiff pole).comp hf)

omit [TopologicalSpace M] [ChartedSpace Plane M] in
theorem sphericalLift_norm (pole : UnitSphere) (f : M → ThreeSpace) (p : M) :
    ‖sphericalLift pole f p‖ = 1 :=
  norm_eq_of_mem_sphere ((stereographic' 3 pole).symm (f p))

omit [TopologicalSpace M] [ChartedSpace Plane M] in
theorem sphericalLift_injective (pole : UnitSphere) {f : M → ThreeSpace}
    (hf : Function.Injective f) : Function.Injective (sphericalLift pole f) :=
  Subtype.val_injective.comp ((stereographic_inverse_injective pole).comp hf)

theorem sphericalLift_mfderiv_injective (pole : UnitSphere) {f : M → ThreeSpace}
    (hf : ContMDiff planeModel threeModel ∞ f)
    (himm : ∀ p, Function.Injective (mfderiv planeModel threeModel f p)) (p : M) :
    Function.Injective (mfderiv planeModel spaceModel (sphericalLift pole f) p) := by
  have hs := stereographic_inverse_contMDiff pole
  have hc : ContMDiff (𝓡 3) spaceModel ∞ (Subtype.val : UnitSphere → Space) :=
    contMDiff_coe_sphere
  have hcinj : Function.Injective (mfderiv (𝓡 3) spaceModel
      (Subtype.val : UnitSphere → Space) ((stereographic' 3 pole).symm (f p))) := by
    intro u v huv
    apply injective_mvfderiv_subtypeVal_sphere ((stereographic' 3 pole).symm (f p))
    exact congrArg (NormedSpace.fromTangentSpace _) huv
  change Function.Injective (mfderiv planeModel spaceModel
    (Subtype.val ∘ (stereographic' 3 pole).symm ∘ f) p)
  rw [mfderiv_comp p ((hc _).mdifferentiableAt (by simp))
    ((hs.comp hf p).mdifferentiableAt (by simp))]
  rw [mfderiv_comp p ((hs _).mdifferentiableAt (by simp))
    ((hf p).mdifferentiableAt (by simp))]
  exact hcinj.comp ((stereographic_inverse_mfderiv_injective pole (f p)).comp (himm p))

theorem exists_spherical_embedding_of_three_embedding {f : M → ThreeSpace}
    (hf : ContMDiff planeModel threeModel ∞ f) (hfinj : Function.Injective f)
    (himm : ∀ p, Function.Injective (mfderiv planeModel threeModel f p)) :
    ∃ I : M → Space, ContMDiff planeModel spaceModel ∞ I ∧
      (∀ p, ‖I p‖ = 1) ∧
      (∀ p, Function.Injective (mfderiv planeModel spaceModel I p)) ∧
      Function.Injective I := by
  exact ⟨sphericalLift sphericalPole f, sphericalLift_contMDiff _ hf,
    sphericalLift_norm _ _, sphericalLift_mfderiv_injective _ hf himm,
    sphericalLift_injective _ hfinj⟩

end R4Embedding
