import R4Embedding.PolynomialOrientation
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! Stage 01 (specification): the hypotheses of the complete target can be met.

`ClosedOrientableSurfaceEmbeddingStatement` quantifies over closed orientable smooth surfaces and
over all smooth metrics on them. This module shows that the quantifiers are not vacuous: the sphere
model `PolynomialLevel 0` is a closed orientable smooth surface (its actual atlas), and it carries a
smooth metric, the one induced from `ℝ³` by its inclusion. The induced metric of any smooth
immersion into an inner product space is constructed in general (`pullbackSmoothMetric`); the
pinned Mathlib has no existence theorem for smooth Riemannian metrics.

The module is not imported by the final theorem; it only checks the statement. -/

noncomputable section
namespace R4Embedding

open Bundle Manifold Set Function
open scoped ContDiff Manifold Topology

section Pullback

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Model norms on the tangent fibers (as in `R4Embedding/OpenMetric.lean`), used only for the
-- boundedness of the unit ball of the induced scalar product.
local instance pullbackTangentNorm (p : M) : NormedAddCommGroup (TangentSpace planeModel p) :=
  inferInstanceAs (NormedAddCommGroup Plane)

local instance pullbackTangentNormSpace (p : M) : NormedSpace ℝ (TangentSpace planeModel p) :=
  inferInstanceAs (NormedSpace ℝ Plane)

local instance pullbackTangentFiniteDimensional (p : M) :
    FiniteDimensional ℝ (TangentSpace planeModel p) :=
  inferInstanceAs (FiniteDimensional ℝ Plane)

/-- The real inner product as a real-bilinear continuous map (`innerSL ℝ` is stated with the
trivial conjugation `→L⋆[ℝ]`, which is not syntactically real-linear). -/
def realInnerSL : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ

omit [IsManifold planeModel ∞ M] in
theorem realInnerSL_apply (v w : E) : realInnerSL v w = inner ℝ v w := rfl

/-- The derivative of a map into a normed space, read in the space itself. -/
def ambientDerivative (f : M → E) (p : M) : TangentSpace planeModel p →L[ℝ] E :=
  (NormedSpace.fromTangentSpace (f p)).toContinuousLinearMap.comp
    (mfderiv planeModel 𝓘(ℝ, E) f p)

/-- The bilinear form `⟪df v, df w⟫` of a map into an inner product space. -/
def pullbackInner (f : M → E) (p : M) :
    TangentSpace planeModel p →L[ℝ] TangentSpace planeModel p →L[ℝ] ℝ :=
  ((ambientDerivative f p).precomp ℝ).comp (realInnerSL.comp (ambientDerivative f p))

omit [IsManifold planeModel ∞ M] in
theorem pullbackInner_apply (f : M → E) (p : M) (v w : TangentSpace planeModel p) :
    pullbackInner f p v w = inner ℝ (ambientDerivative f p v) (ambientDerivative f p w) := rfl

theorem pullbackInner_contMDiff {f : M → E} (hf : ContMDiff planeModel 𝓘(ℝ, E) ∞ f) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ, Plane →L[ℝ] Plane →L[ℝ] ℝ)) ∞
      (fun b ↦ TotalSpace.mk' (Plane →L[ℝ] Plane →L[ℝ] ℝ)
        (E := fun b : M ↦ TangentSpace planeModel b →L[ℝ] TangentSpace planeModel b →L[ℝ] ℝ)
        b (pullbackInner f b)) := by
  intro x₀
  rw [contMDiffAt_section]
  have hA : ContMDiffAt planeModel 𝓘(ℝ, Plane →L[ℝ] E) ∞
      (inTangentCoordinates planeModel 𝓘(ℝ, E) id f
        (fun x ↦ mfderiv planeModel 𝓘(ℝ, E) f x) x₀) x₀ :=
    (hf x₀).mfderiv_const (by simp)
  have hP : ContMDiffAt planeModel 𝓘(ℝ, (E →L[ℝ] ℝ) →L[ℝ] (Plane →L[ℝ] ℝ)) ∞
      (fun x ↦ ((inTangentCoordinates planeModel 𝓘(ℝ, E) id f
        (fun x ↦ mfderiv planeModel 𝓘(ℝ, E) f x) x₀ x).precomp ℝ :
          (E →L[ℝ] ℝ) →L[ℝ] (Plane →L[ℝ] ℝ))) x₀ :=
    hA.clm_precomp
  have hQ : ContMDiffAt planeModel 𝓘(ℝ, Plane →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun x ↦ (realInnerSL (E := E)).comp (inTangentCoordinates planeModel 𝓘(ℝ, E) id f
        (fun x ↦ mfderiv planeModel 𝓘(ℝ, E) f x) x₀ x)) x₀ :=
    contMDiffAt_const.clm_comp hA
  apply (hP.clm_comp hQ).congr_of_eventuallyEq
  filter_upwards [(chartAt Plane x₀).open_source.mem_nhds (mem_chart_source Plane x₀)] with x hx
  have hb : x ∈ (trivializationAt (Plane →L[ℝ] ℝ)
      (fun x ↦ TangentSpace planeModel x →L[ℝ] ℝ) x₀).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨by simpa using hx, by simp⟩
  ext v w
  simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, inTangentCoordinates,
    ContinuousLinearMap.comp_apply, Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hb,
    TangentBundle.continuousLinearMapAt_model_space]
  simp [pullbackInner, ambientDerivative, realInnerSL, NormedSpace.fromTangentSpace]
  rfl

omit [IsManifold planeModel ∞ M] in
theorem ambientDerivative_injective {f : M → E} {p : M}
    (h : Function.Injective (mfderiv planeModel 𝓘(ℝ, E) f p)) :
    Function.Injective (ambientDerivative f p) :=
  fun _ _ hvw => h ((NormedSpace.fromTangentSpace (f p)).injective hvw)

/-- The metric induced by a smooth immersion into an inner product space. -/
def pullbackSmoothMetric {f : M → E} (hf : ContMDiff planeModel 𝓘(ℝ, E) ∞ f)
    (himm : ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ, E) f p)) : SmoothMetric M where
  inner := pullbackInner f
  symm p v w := by simp only [pullbackInner_apply, real_inner_comm]
  pos p v hv := by
    rw [pullbackInner_apply, real_inner_self_eq_norm_sq]
    have h : ambientDerivative f p v ≠ 0 := fun h0 =>
      hv (ambientDerivative_injective (himm p) (h0.trans (map_zero _).symm))
    exact pow_pos (norm_pos_iff.mpr h) 2
  isVonNBounded p := by
    obtain ⟨K, -, hK⟩ := (LinearMap.injective_iff_antilipschitz
      (ambientDerivative f p : TangentSpace planeModel p →ₗ[ℝ] E)).mp
      (ambientDerivative_injective (himm p))
    refine NormedSpace.isVonNBounded_of_isBounded ℝ
      ((Metric.isBounded_closedBall (x := (0 : TangentSpace planeModel p)) (r := K)).subset ?_)
    intro v hv
    simp only [Set.mem_ofPred_eq, pullbackInner_apply, real_inner_self_eq_norm_sq] at hv
    have h1 : ‖ambientDerivative f p v‖ ≤ 1 := by
      nlinarith [norm_nonneg (ambientDerivative f p v)]
    have h2 := hK.le_mul_dist v 0
    simp only [dist_zero_right, map_zero, ContinuousLinearMap.coe_coe] at h2
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖v‖ ≤ K * ‖ambientDerivative f p v‖ := h2
      _ ≤ K * 1 := by gcongr
      _ = K := mul_one _
  contMDiff := pullbackInner_contMDiff hf

end Pullback

/-- Every polynomial model carries a smooth metric, induced from `ℝ³`. -/
theorem polynomialLevel_smoothMetric_nonempty (g : ℕ) :
    let _ := polynomialLevelChartedSpace g
    let _ := polynomialLevel_isManifold g
    Nonempty (SmoothMetric (PolynomialLevel g)) := by
  let _ := polynomialLevelChartedSpace g
  let _ := polynomialLevel_isManifold g
  obtain ⟨f, hf, -, himm⟩ := polynomialLevel_initial_three_embedding g
  exact ⟨pullbackSmoothMetric hf himm⟩

/-- The hypotheses of the complete target can all be met: there is a closed orientable smooth
surface carrying a smooth metric (the sphere model, with the metric induced from `ℝ³`). -/
theorem closedOrientableSurface_hypotheses_satisfiable :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace Plane M)
      (_ : IsManifold planeModel ∞ M) (_ : CompactSpace M) (_ : T2Space M),
      IsOrientableSurface M ∧ Nonempty (SmoothMetric M) :=
  ⟨PolynomialLevel 0, inferInstance, polynomialLevelChartedSpace 0, polynomialLevel_isManifold 0,
    polynomialLevel_compactSpace 0, inferInstance, polynomialLevel_isOrientable 0,
    polynomialLevel_smoothMetric_nonempty 0⟩

end R4Embedding
