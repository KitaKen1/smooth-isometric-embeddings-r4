import R4Embedding.ComponentAssembly
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Restrict the given smooth metric to an open surface using the actual
derivative of the inclusion. This retains the original metric and atlas. -/

noncomputable section
namespace R4Embedding

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

open Bundle Manifold Set Filter Bornology TopologicalSpace
open scoped ContDiff Topology

abbrev MetricCoefficients := Plane →L[ℝ] Plane →L[ℝ] ℝ

variable {N : Type*} [TopologicalSpace N] [ChartedSpace Plane N]

theorem contMDiffAt_bilinearComp {G : N → MetricCoefficients} {A : N → Plane →L[ℝ] Plane}
    {p : N} (hG : ContMDiffAt planeModel 𝓘(ℝ, MetricCoefficients) ∞ G p)
    (hA : ContMDiffAt planeModel 𝓘(ℝ, Plane →L[ℝ] Plane) ∞ A p) :
    ContMDiffAt planeModel 𝓘(ℝ, MetricCoefficients) ∞
      (fun q => (G q).bilinearComp (A q) (A q)) p := by
  have h := hA.clm_precomp (F₃ := ℝ) |>.clm_comp (hG.clm_comp hA)
  convert h using 1
  ext q v w
  rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

-- Auxiliary model norms are used only to form bilinear operator composition.
-- The scalar product below is the original metric pulled back by the inclusion.
local instance tangentModelNorm {P : Type*} [TopologicalSpace P] [ChartedSpace Plane P]
    (p : P) : NormedAddCommGroup (TangentSpace planeModel p) :=
  inferInstanceAs (NormedAddCommGroup Plane)

local instance tangentModelNormSpace {P : Type*} [TopologicalSpace P] [ChartedSpace Plane P]
    (p : P) : NormedSpace ℝ (TangentSpace planeModel p) :=
  inferInstanceAs (NormedSpace ℝ Plane)

local instance tangentFiniteDimensional {P : Type*} [TopologicalSpace P]
    [ChartedSpace Plane P] (p : P) : FiniteDimensional ℝ (TangentSpace planeModel p) :=
  inferInstanceAs (FiniteDimensional ℝ Plane)

def openPullbackInner (U : Opens M) (g : SmoothMetric M) (p : U) :
    TangentSpace planeModel p →L[ℝ] TangentSpace planeModel p →L[ℝ] ℝ :=
  (g.inner p.val).bilinearComp
    (mfderiv planeModel planeModel (Subtype.val : U → M) p)
    (mfderiv planeModel planeModel (Subtype.val : U → M) p)

theorem tangentBilinearCoefficients_apply (p₀ p : M)
    (G : TangentSpace planeModel p →L[ℝ] TangentSpace planeModel p →L[ℝ] ℝ)
    (hp : p ∈ (trivializationAt Plane (TangentSpace planeModel) p₀).baseSet)
    (v w : Plane) :
    (trivializationAt MetricCoefficients
      (fun q : M => TangentSpace planeModel q →L[ℝ] TangentSpace planeModel q →L[ℝ] ℝ)
      p₀ ⟨p, G⟩).2 v w =
      G ((trivializationAt Plane (TangentSpace planeModel) p₀).symmL ℝ p v)
        ((trivializationAt Plane (TangentSpace planeModel) p₀).symmL ℝ p w) := by
  rw [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ hp hp (by simp)]
  simp only [Trivialization.symmL_apply _ hp]
  simp

theorem openPullbackInner_contMDiff (U : Opens M) (g : SmoothMetric M) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ, MetricCoefficients)) ∞
      (fun p => TotalSpace.mk' MetricCoefficients p (openPullbackInner U g p)) := by
  intro p₀
  apply (contMDiffAt_section p₀).mpr
  let A := fun p : U => mfderiv planeModel planeModel (Subtype.val : U → M) p
  let G := fun p : U => (trivializationAt MetricCoefficients
    (fun q : M => TangentSpace planeModel q →L[ℝ] TangentSpace planeModel q →L[ℝ] ℝ)
    p₀.val ⟨p.val, g.inner p.val⟩).2
  let a := inTangentCoordinates planeModel planeModel id (Subtype.val : U → M) A p₀
  have hG : ContMDiffAt planeModel 𝓘(ℝ, MetricCoefficients) ∞ G p₀ :=
    ((contMDiffAt_section p₀.val).mp (g.contMDiff p₀.val)).comp p₀
      (contMDiff_subtype_val (I := planeModel) (n := ∞) p₀)
  have ha : ContMDiffAt planeModel 𝓘(ℝ, Plane →L[ℝ] Plane) ∞ a p₀ :=
    (contMDiff_subtype_val (I := planeModel) (n := ∞) p₀).mfderiv_const (by simp)
  apply (contMDiffAt_bilinearComp hG ha).congr_of_eventuallyEq
  have hbase : ∀ᶠ p : U in 𝓝 p₀,
      p.val ∈ (trivializationAt Plane (TangentSpace planeModel) p₀.val).baseSet :=
    continuous_subtype_val.continuousAt
      ((trivializationAt Plane (TangentSpace planeModel) p₀.val).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt Plane (TangentSpace planeModel) p₀.val))
  have hsource : ∀ᶠ p : U in 𝓝 p₀,
      p ∈ (trivializationAt Plane (TangentSpace planeModel) p₀).baseSet :=
    (trivializationAt Plane (TangentSpace planeModel) p₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt Plane (TangentSpace planeModel) p₀)
  filter_upwards [hbase, hsource] with p hp hps
  ext v w
  rw [tangentBilinearCoefficients_apply p₀ p _ hps]
  change openPullbackInner U g p _ _ = (G p).bilinearComp (a p) (a p) v w
  rw [ContinuousLinearMap.bilinearComp_apply]
  dsimp only [G]
  rw [tangentBilinearCoefficients_apply p₀.val p.val _ hp]
  simp only [a, A, inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply, openPullbackInner, ContinuousLinearMap.bilinearComp_apply]
  simp only [Trivialization.symmL_continuousLinearMapAt _ hp]
  rfl

def openSubtypeTangentEquiv (U : Opens M) (p : U) :
    TangentSpace planeModel p ≃L[ℝ] TangentSpace planeModel p.val :=
  (LinearEquiv.ofBijective
    (mfderiv planeModel planeModel (Subtype.val : U → M) p).toLinearMap
    ⟨(IsImmersion.of_opens (I := planeModel) (n := ∞) U).injective_mfderiv (by simp) p,
      openSubtype_mfderiv_surjective U p⟩).toContinuousLinearEquiv

theorem openSubtypeTangentEquiv_apply (U : Opens M) (p : U)
    (v : TangentSpace planeModel p) :
    openSubtypeTangentEquiv U p v =
      mfderiv planeModel planeModel (Subtype.val : U → M) p v := rfl

theorem openPullbackInner_isVonNBounded (U : Opens M) (g : SmoothMetric M) (p : U) :
    IsVonNBounded ℝ {v : TangentSpace planeModel p | openPullbackInner U g p v v < 1} := by
  let e := openSubtypeTangentEquiv U p
  apply ((g.isVonNBounded p.val).image e.symm.toContinuousLinearMap).subset
  intro v hv
  refine ⟨e v, ?_, ?_⟩
  · exact hv
  · exact e.symm_apply_apply v

def restrictSmoothMetric (U : Opens M) (g : SmoothMetric M) : SmoothMetric U where
  inner := openPullbackInner U g
  symm p v w := g.symm p.val _ _
  pos p v hv := by
    apply g.pos p.val
    intro hzero
    apply hv
    apply (openSubtypeTangentEquiv U p).injective
    change (mfderiv planeModel planeModel (Subtype.val : U → M) p) v =
      (mfderiv planeModel planeModel (Subtype.val : U → M) p) 0
    rw [map_zero]
    exact hzero
  isVonNBounded := openPullbackInner_isVonNBounded U g
  contMDiff := openPullbackInner_contMDiff U g

theorem restrictSmoothMetric_inner (U : Opens M) (g : SmoothMetric M) (p : U)
    (v w : TangentSpace planeModel p) :
    (restrictSmoothMetric U g).inner p v w =
      g.inner p.val
        (mfderiv planeModel planeModel (Subtype.val : U → M) p v)
        (mfderiv planeModel planeModel (Subtype.val : U → M) p w) := rfl

theorem exists_isometric_embedding_of_component_embeddings [CompactSpace M]
    (g : SmoothMetric M)
    (hcomponent : ∀ c : ConnectedComponents M, ∃ f : componentOpen c → Space,
      IsSmoothIsometricEmbedding (restrictSmoothMetric (componentOpen c) g) f) :
    ∃ F : M → Space, IsSmoothIsometricEmbedding g F := by
  apply exists_isometric_embedding_of_component_maps g
  intro c
  obtain ⟨f, hf⟩ := hcomponent c
  refine ⟨f, hf.1.1, hf.2, ?_⟩
  intro p v w
  exact hf.1.2 p v w

end R4Embedding
