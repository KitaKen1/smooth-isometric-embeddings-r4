import R4Analytic.AnalyticBoundaryProfileTransfer
import R4Analytic.AnalyticMetricSpec
import OAI.Geometry.SurfaceImmersion.Primitive.SurfaceCircularThreshold

/-! Apply circular-family extraction to the actual surface jet. The family
translation, radius, frame and phase are read from the original jetSection;
the certificate refers to the same output W as the five-profile estimate. -/

noncomputable section
namespace R4Embedding

open scoped Matrix ContDiff
open OAI.ClosedSurfaceR4

theorem analytic_first_profile_of_five_profiles
    {F W : (ℝ × ℝ) → RawVector} {a : (ℝ × ℝ) → ℝ}
    {e₁ e₂ : SurfaceVelocityFamily.GeometricJet → RawVector}
    {α : SurfaceVelocityFamily.GeometricJet × ℝ → ℝ}
    {x : ℝ × ℝ} {z t ε : ℝ}
    (hD : NormalFrame.gramDet (SmallModes.coordDeriv SmallModes.dy F x)
      (SmallModes.coordDeriv SmallModes.dy (SmallModes.coordDeriv SmallModes.dy F) x) ≠ 0)
    (hframe : let j := CollarVelocity.jetSection F x
      j.2 1 ⬝ᵥ e₁ j = 0 ∧ j.2 4 ⬝ᵥ e₁ j = 0 ∧
      j.2 1 ⬝ᵥ e₂ j = 0 ∧ j.2 4 ⬝ᵥ e₂ j = 0)
    (hclose : ‖GeometryPreservation.realBoundaryProfile W z x -
      SurfaceVelocityFamily.surfaceCircularProfile F a e₁ e₂ α (x,t)‖ < ε) :
    AnalyticFirstProfileEstimate F W x ε := by
  apply analytic_first_profile_of_circular_family
    (Q := fun q => SmallModes.coordDeriv SmallModes.dx F q -
      SurfaceVelocityFamily.jetNormal (CollarVelocity.jetSection F q))
    (R := fun q => VelocityFrame.velocityRadius
      (SurfaceVelocityFamily.jetNormal (CollarVelocity.jetSection F q)) (a q))
    (e₁ := e₁ ∘ CollarVelocity.jetSection F)
    (e₂ := e₂ ∘ CollarVelocity.jetSection F)
    (α := fun q => α (CollarVelocity.jetSection F q.1, q.2)) hD
  · exact hframe
  · exact hclose

end R4Embedding
