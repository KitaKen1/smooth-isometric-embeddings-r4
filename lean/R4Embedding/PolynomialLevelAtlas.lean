import R4Embedding.ModelChartSource
import R4ModelAtlas.LevelAtlas

/-! Concrete polynomial levels with their actual constructed atlas.
Genus, orientability and smooth classification of arbitrary supplied atlases
are deliberately separate obligations. Integrated after the standalone reduced-atlas and eight-entry audits succeeded.
The default build audits all declarations and snapshots the actual atlas sources.
-/

set_option autoImplicit false
noncomputable section
namespace R4Embedding

open Manifold
open scoped Manifold ContDiff
open R4ModelAtlas.RegularLevel

abbrev PolynomialLevel (g : ℕ) := {p : ModelAmbient // modelPolynomial g p = 0}

@[reducible]
def polynomialLevelRawChartedSpace (g : ℕ) : ChartedSpace RawModelPlane (PolynomialLevel g) :=
  levelChartedSpace (m := 2) 𝓘(ℝ, ModelAmbient)
    (modelPolynomial_contMDiff g) (modelPolynomial_mfderiv_ne_zero g)

theorem polynomialLevel_compactSpace (g : ℕ) : CompactSpace (PolynomialLevel g) :=
  isCompact_iff_compactSpace.mp (modelPolynomial_level_compact g)

theorem polynomialLevel_nonempty (g : ℕ) : Nonempty (PolynomialLevel g) := by
  obtain ⟨p, hp⟩ := modelPolynomial_level_nonempty g
  exact ⟨⟨p, hp⟩⟩

theorem polynomialLevelRaw_isManifold (g : ℕ) :
    let _ := polynomialLevelRawChartedSpace g
    IsManifold 𝓘(ℝ, RawModelPlane) ∞ (PolynomialLevel g) := by
  let _ := polynomialLevelRawChartedSpace g
  exact levelIsManifold (m := 2) 𝓘(ℝ, ModelAmbient)
    (modelPolynomial_contMDiff g) (modelPolynomial_mfderiv_ne_zero g)

theorem polynomialLevelRaw_inclusion_contMDiff (g : ℕ) :
    let _ := polynomialLevelRawChartedSpace g
    ContMDiff 𝓘(ℝ, RawModelPlane) 𝓘(ℝ, ModelAmbient) ∞
      (Subtype.val : PolynomialLevel g → ModelAmbient) := by
  let _ := polynomialLevelRawChartedSpace g
  exact contMDiff_level_inclusion (m := 2) 𝓘(ℝ, ModelAmbient)
    (modelPolynomial_contMDiff g) (modelPolynomial_mfderiv_ne_zero g)

theorem polynomialLevelRaw_inclusion_mfderiv_injective (g : ℕ) :
    let _ := polynomialLevelRawChartedSpace g
    ∀ p, Function.Injective (mfderiv 𝓘(ℝ, RawModelPlane) 𝓘(ℝ, ModelAmbient)
      (Subtype.val : PolynomialLevel g → ModelAmbient) p) := by
  let _ := polynomialLevelRawChartedSpace g
  dsimp only []
  intro p
  exact (isSmoothEmbedding_level_inclusion (m := 2) 𝓘(ℝ, ModelAmbient)
    (modelPolynomial_contMDiff g) (modelPolynomial_mfderiv_ne_zero g)).isImmersion.injective_mfderiv
      (by simp) p

@[reducible]
def polynomialLevelChartedSpace (g : ℕ) : ChartedSpace Plane (PolynomialLevel g) :=
  let _ := polynomialLevelRawChartedSpace g
  chartedSpaceTransHomeomorph rawModelPlaneToPlane.toHomeomorph

theorem polynomialLevel_isManifold (g : ℕ) :
    let _ := polynomialLevelChartedSpace g
    IsManifold planeModel ∞ (PolynomialLevel g) := by
  let _ := polynomialLevelRawChartedSpace g
  let _ := polynomialLevelRaw_isManifold g
  exact isManifold_transHomeomorph (M := PolynomialLevel g) 𝓘(ℝ, RawModelPlane) planeModel
    rawModelPlaneToPlane.toHomeomorph rawModelPlaneToPlane (fun _ => rfl)

theorem polynomialLevel_initial_three_embedding (g : ℕ) :
    let _ := polynomialLevelChartedSpace g
    ∃ f : PolynomialLevel g → ThreeSpace, ContMDiff planeModel threeModel ∞ f ∧
      Function.Injective f ∧ ∀ p, Function.Injective (mfderiv planeModel threeModel f p) := by
  let _ := polynomialLevelRawChartedSpace g
  let _ := polynomialLevelRaw_isManifold g
  refine ⟨rawModelAmbientToThree ∘ Subtype.val, ?_⟩
  exact initialThreeEmbedding_of_raw_model
    (polynomialLevelRaw_inclusion_contMDiff g) Subtype.val_injective
    (polynomialLevelRaw_inclusion_mfderiv_injective g)

theorem polynomialLevel_initial_spherical_embedding (g : ℕ) :
    let _ := polynomialLevelChartedSpace g
    ∃ f : PolynomialLevel g → Space, ContMDiff planeModel spaceModel ∞ f ∧
      (∀ p, ‖f p‖ = 1) ∧ (∀ p, Function.Injective (mfderiv planeModel spaceModel f p)) ∧
      Function.Injective f := by
  let _ := polynomialLevelChartedSpace g
  let _ := polynomialLevel_isManifold g
  obtain ⟨f, hs, hi, hm⟩ := polynomialLevel_initial_three_embedding g
  exact exists_spherical_embedding_of_three_embedding hs hi hm

end R4Embedding
