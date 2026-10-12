import R4Embedding.ModelChartTransport
import R4Embedding.InitialPolynomialModel
import R4Embedding.SphericalTransfer
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! The identity between linearly related model charts has an explicit
derivative. This is used for newly constructed regular-level models; it does
not replace or classify the supplied smooth atlas of an arbitrary surface. -/

set_option autoImplicit false
noncomputable section
namespace R4Embedding

open Manifold Filter Function
open scoped Topology ContDiff Manifold

section SourceChange
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]
  (L : E ≃L[ℝ] F)

theorem linearChart_identity_coordinates (x : M) :
    let _ := chartedSpaceTransHomeomorph (M := M) L.toHomeomorph
    (extChartAt 𝓘(ℝ, E) x ∘ id ∘ (extChartAt 𝓘(ℝ, F) x).symm) =ᶠ[
      𝓝 (extChartAt 𝓘(ℝ, F) x x)] L.symm := by
  let _ := chartedSpaceTransHomeomorph (M := M) L.toHomeomorph
  dsimp only []
  have hchart : ⇑(extChartAt 𝓘(ℝ, F) x) = L ∘ ⇑(extChartAt 𝓘(ℝ, E) x) :=
    coe_extChartAt_chartedSpaceTransHomeomorph 𝓘(ℝ, E) 𝓘(ℝ, F)
      L.toHomeomorph L (fun _ => rfl) x
  filter_upwards [extChartAt_target_mem_nhds (I := 𝓘(ℝ, F)) x] with y hy
  apply L.injective
  simpa only [hchart, comp_apply, id_eq, ContinuousLinearEquiv.apply_symm_apply] using
    (extChartAt 𝓘(ℝ, F) x).right_inv hy

theorem linearChart_identity_contMDiff :
    let _ := chartedSpaceTransHomeomorph (M := M) L.toHomeomorph
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ (id : M → M) := by
  let _ := chartedSpaceTransHomeomorph (M := M) L.toHomeomorph
  dsimp only []
  intro x
  rw [contMDiffAt_iff]
  refine ⟨continuous_id.continuousAt, ?_⟩
  exact (L.symm.contDiff.contDiffAt.congr_of_eventuallyEq
    (linearChart_identity_coordinates L x)).contDiffWithinAt

theorem linearChart_identity_hasMFDerivAt (x : M) :
    let _ := chartedSpaceTransHomeomorph (M := M) L.toHomeomorph
    HasMFDerivAt 𝓘(ℝ, F) 𝓘(ℝ, E) (id : M → M) x L.symm.toContinuousLinearMap := by
  let _ := chartedSpaceTransHomeomorph (M := M) L.toHomeomorph
  dsimp only []
  refine ⟨continuous_id.continuousAt, ?_⟩
  exact ((L.symm.hasFDerivAt (x := extChartAt 𝓘(ℝ, F) x x)).congr_of_eventuallyEq
    (linearChart_identity_coordinates L x)).hasFDerivWithinAt

variable {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
  (K : ModelWithCorners ℝ G H)

theorem contMDiff_of_linear_model_change {f : M → N}
    (hf : ContMDiff 𝓘(ℝ, E) K ∞ f) :
    let _ := chartedSpaceTransHomeomorph (M := M) L.toHomeomorph
    ContMDiff 𝓘(ℝ, F) K ∞ f := by
  let _ := chartedSpaceTransHomeomorph (M := M) L.toHomeomorph
  dsimp only []
  simpa only [comp_id] using hf.comp (linearChart_identity_contMDiff L)

theorem mfderiv_of_linear_model_change {f : M → N}
    (hf : ContMDiff 𝓘(ℝ, E) K ∞ f) (x : M) :
    let _ := chartedSpaceTransHomeomorph (M := M) L.toHomeomorph
    mfderiv 𝓘(ℝ, F) K f x =
      (mfderiv 𝓘(ℝ, E) K f x).comp L.symm.toContinuousLinearMap := by
  let _ := chartedSpaceTransHomeomorph (M := M) L.toHomeomorph
  dsimp only []
  have h := mfderiv_comp x ((hf x).mdifferentiableAt (by simp))
    ((linearChart_identity_contMDiff L x).mdifferentiableAt (by simp))
  rw [(linearChart_identity_hasMFDerivAt L x).mfderiv] at h
  simp only [comp_id, id_eq] at h
  convert h using 1
  rfl

theorem mfderiv_injective_of_linear_model_change {f : M → N}
    (hf : ContMDiff 𝓘(ℝ, E) K ∞ f)
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) K f x)) :
    let _ := chartedSpaceTransHomeomorph (M := M) L.toHomeomorph
    ∀ x, Function.Injective (mfderiv 𝓘(ℝ, F) K f x) := by
  let _ := chartedSpaceTransHomeomorph (M := M) L.toHomeomorph
  dsimp only []
  intro x
  rw [mfderiv_of_linear_model_change L K hf x]
  exact (hi x).comp L.symm.injective

end SourceChange

abbrev RawModelPlane := Fin 2 → ℝ

def rawModelPlaneToPlane : RawModelPlane ≃L[ℝ] Plane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm

def rawModelAmbientToThree : ModelAmbient ≃L[ℝ] ThreeSpace :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm

theorem initialThreeEmbedding_of_raw_model
    {M : Type*} [TopologicalSpace M] [ChartedSpace RawModelPlane M]
    [IsManifold 𝓘(ℝ, RawModelPlane) ∞ M]
    {f : M → ModelAmbient} (hs : ContMDiff 𝓘(ℝ, RawModelPlane) 𝓘(ℝ, ModelAmbient) ∞ f)
    (hi : Function.Injective f)
    (hm : ∀ p, Function.Injective (mfderiv 𝓘(ℝ, RawModelPlane) 𝓘(ℝ, ModelAmbient) f p)) :
    let _ := chartedSpaceTransHomeomorph (M := M) rawModelPlaneToPlane.toHomeomorph
    ContMDiff planeModel threeModel ∞ (rawModelAmbientToThree ∘ f) ∧
      Function.Injective (rawModelAmbientToThree ∘ f) ∧
      ∀ p, Function.Injective (mfderiv planeModel threeModel (rawModelAmbientToThree ∘ f) p) := by
  let _ := chartedSpaceTransHomeomorph (M := M) rawModelPlaneToPlane.toHomeomorph
  dsimp only []
  let _ : IsManifold planeModel ∞ M :=
    isManifold_transHomeomorph (M := M) 𝓘(ℝ, RawModelPlane) planeModel
    rawModelPlaneToPlane.toHomeomorph rawModelPlaneToPlane (fun _ => rfl)
  have hsource := contMDiff_of_linear_model_change rawModelPlaneToPlane 𝓘(ℝ, ModelAmbient) hs
  have hderiv := mfderiv_injective_of_linear_model_change
    rawModelPlaneToPlane 𝓘(ℝ, ModelAmbient) hs hm
  refine ⟨rawModelAmbientToThree.toDiffeomorph.contMDiff.comp hsource,
    rawModelAmbientToThree.injective.comp hi, ?_⟩
  intro p
  change Function.Injective (mfderiv planeModel threeModel
    (rawModelAmbientToThree.toDiffeomorph ∘ f) p)
  rw [mfderiv_comp p
    (rawModelAmbientToThree.toDiffeomorph.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    ((hsource p).mdifferentiableAt (by simp))]
  exact ((rawModelAmbientToThree.toDiffeomorph.isInvertible_mfderiv (x := f p)
    (by simp)).injective).comp (hderiv p)

end R4Embedding
