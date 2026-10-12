import R4Embedding.CoordinateSurfaceGeometry
import R4Embedding.CoordinateNorms

/-! A genuine equality on a neighbourhood transfers the first and second
coordinate derivatives. This covers support boundaries whenever the outer
cutoff is locally one; a nonzero inner weight is unnecessary. -/

noncomputable section
namespace R4Embedding

open Filter
open scoped Topology ContDiff

theorem coordinate_first_and_yy_of_raw_germ {F : (ℝ × ℝ) → Space}
    {G : (ℝ × ℝ) → RawVector} {x : ℝ × ℝ}
    (hG : ContDiff ℝ ∞ G) (hg : G =ᶠ[𝓝 x] rawToSpace.symm ∘ F) :
    (∀ v : ℝ × ℝ, fderiv ℝ G x v = rawToSpace.symm (fderiv ℝ F x v)) ∧
    fderiv ℝ (fun q => fderiv ℝ G q (0, 1)) x (0, 1) =
      rawToSpace.symm (coordinateSurfaceYY F x) := by
  have hcoord (q : ℝ × ℝ) (hq : G =ᶠ[𝓝 q] rawToSpace.symm ∘ F) :
      ContDiffAt ℝ ∞ F q := by
    have he : rawToSpace ∘ G =ᶠ[𝓝 q] F := by
      filter_upwards [hq] with y hy
      simp only [Function.comp_apply, hy, ContinuousLinearEquiv.apply_symm_apply]
    exact ((rawToSpace.contDiff.comp hG).contDiffAt).congr_of_eventuallyEq he.symm
  have hfirst (q : ℝ × ℝ) (hq : G =ᶠ[𝓝 q] rawToSpace.symm ∘ F) (v : ℝ × ℝ) :
      fderiv ℝ G q v = rawToSpace.symm (fderiv ℝ F q v) := by
    have hchain := (rawToSpace.symm.hasFDerivAt.comp q
      ((hcoord q hq).differentiableAt (by simp)).hasFDerivAt).fderiv
    have hsame := hq.fderiv_eq (𝕜 := ℝ)
    rw [hchain] at hsame
    exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] RawVector => L v) hsame
  refine ⟨hfirst x hg, ?_⟩
  have hy : (fun q => fderiv ℝ G q (0, 1)) =ᶠ[𝓝 x]
      rawToSpace.symm ∘ coordinateSurfaceY F := by
    filter_upwards [hg.eventually_nhds] with q hq
    exact hfirst q hq (0, 1)
  have hY := (coordinateSurfaceY_contDiffAt (hcoord x hg)).differentiableAt (by simp)
  have hchain := (rawToSpace.symm.hasFDerivAt.comp x hY.hasFDerivAt).fderiv
  have hsame := hy.fderiv_eq (𝕜 := ℝ)
  rw [hchain] at hsame
  exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] RawVector => L (0, 1)) hsame

end R4Embedding
