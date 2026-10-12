import R4Embedding.CoordinateMetric
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! Smoothness of the parametrization and of the standard metric supplies
the coefficient continuity required by the uniform derivative bound. -/

noncomputable section

namespace R4Embedding

open Bundle Manifold Set
open scoped ContDiff

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem continuousOn_coordinate_tangent_lift
    {c : (ℝ × ℝ) → M} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hc : ContMDiffOn pairModel planeModel ∞ c U) (v : ℝ × ℝ) :
    ContinuousOn (fun q => TotalSpace.mk' Plane (c q) (coordinateTangentMap c q v)) U := by
  have hmap := hc.continuousOn_tangentMapWithin (by simp) hU.uniqueMDiffOn
  have hlift : Continuous (fun q : ℝ × ℝ =>
      (⟨q, v⟩ : TangentBundle pairModel (ℝ × ℝ))) :=
    (tangentBundleModelSpaceHomeomorph pairModel).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hcomp := hmap.comp hlift.continuousOn (fun _ hq => hq)
  apply hcomp.congr
  intro q hq
  change (⟨c q, mfderiv pairModel planeModel c q v⟩ : TangentBundle planeModel M) =
    ⟨c q, mfderivWithin pairModel planeModel c U q v⟩
  rw [mfderivWithin_of_isOpen hU hq]

theorem continuousOn_pulled_back_metric_coefficient
    (g : SmoothMetric M) {c : (ℝ × ℝ) → M} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hc : ContMDiffOn pairModel planeModel ∞ c U) (v : ℝ × ℝ) :
    ContinuousOn (fun q => g.inner (c q)
      (coordinateTangentMap c q v) (coordinateTangentMap c q v)) U := by
  have hmetric : ContinuousOn (fun q => TotalSpace.mk' (Plane →L[ℝ] Plane →L[ℝ] ℝ)
      (E := fun p : M => TangentSpace planeModel p →L[ℝ]
        TangentSpace planeModel p →L[ℝ] ℝ)
      (c q) (g.inner (c q))) U :=
    g.contMDiff.continuous.comp_continuousOn hc.continuousOn
  have hv := continuousOn_coordinate_tangent_lift hU hc v
  have hscalar := hmetric.clm_bundle_apply₂ (F₁ := Plane) (F₂ := Plane) (F₃ := ℝ) hv hv
  exact continuous_snd.comp_continuousOn
    ((Bundle.Trivial.homeomorphProd M ℝ).continuous.comp_continuousOn hscalar)

/-- The fixed metric and smooth coordinate map determine B before any output
f. No coefficient-continuity or derivative-bound assumption is left over. -/
theorem exists_uniform_isometric_derivative_bound_on_smooth_coordinates
    (g : SmoothMetric M) (c : (ℝ × ℝ) → M) {U K : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hc : ContMDiffOn pairModel planeModel ∞ c U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ f : M → Space, IsSmoothIsometricMap g f →
      ∀ q ∈ K, ‖fderiv ℝ (f ∘ c) q‖ ≤ B := by
  apply exists_uniform_isometric_chart_derivative_bound g c hK
  · intro q hq
    exact ((hc.mdifferentiableOn (by simp)) q (hKU hq)).mdifferentiableAt
      (hU.mem_nhds (hKU hq))
  · exact (continuousOn_pulled_back_metric_coefficient g hU hc (1, 0)).mono hKU
  · exact (continuousOn_pulled_back_metric_coefficient g hU hc (0, 1)).mono hKU

end R4Embedding
