import R4Embedding.CircularProfiles
import OAI.Geometry.SurfaceImmersion.Primitive.BoundaryProfileFrame
import OAI.Geometry.SurfaceImmersion.Primitive.CircularFamilyProfile
import OAI.Geometry.Immersion.ClosedSurface.ChartModel

/-! Read the genuine five-profile constructors before any jet-loop construction.
The transverse witness is explicit and pointwise. No smooth frame selection,
unit frame, positive radius, or bounds on the remaining three entries are
needed for this implication. All derivative estimates refer to the same map. -/

noncomputable section
namespace R4Embedding

open scoped Matrix ContDiff
open OAI.ClosedSurfaceR4

theorem rawGramDet_eq_analytic (Y C : RawVector) :
    rawGramDet Y C = NormalFrame.gramDet Y C := rfl

theorem rawNormalPart_eq_analytic (Y C X : RawVector) :
    rawNormalPart Y C X = RealModes.realNormalPart Y C X := rfl

theorem rawCircularLeading_eq_analytic (X Y C e₁ e₂ : RawVector) (R α : ℝ) :
    rawCircularLeading X Y C e₁ e₂ R α =
      VelocityFrame.leadingTangent X Y C (R • VelocityFrame.direction e₁ e₂ α) := rfl

theorem rawToSpace_symm_eq_analytic_coordinates (v : Space) :
    rawToSpace.symm v = OAI.ClosedSurfaceR4.spaceCoordinates v := rfl

/-- A pointwise certificate; the transverse vector needs no smooth choice. -/
def AnalyticFirstProfileEstimate (F W : (ℝ × ℝ) → RawVector)
    (x : ℝ × ℝ) (ε : ℝ) : Prop :=
  ∃ w : RawVector,
    w ⬝ᵥ (fderiv ℝ F x (0, 1)) = 0 ∧
    w ⬝ᵥ (fderiv ℝ (fun q => fderiv ℝ F q (0, 1)) x (0, 1)) = 0 ∧
    ‖fderiv ℝ W x (1, 0) - fderiv ℝ F x (1, 0) - w‖ ≤ ε ∧
    ‖fderiv ℝ W x (0, 1) - fderiv ℝ F x (0, 1)‖ ≤ ε

/-- The first two entries of the actual circular family determine the certificate.
The family translation Q and the scaled xx entry of W do not affect the result. -/
theorem analytic_first_profile_of_circular_family
    {F W Q e₁ e₂ : (ℝ × ℝ) → RawVector} {R : (ℝ × ℝ) → ℝ}
    {α : (ℝ × ℝ) × ℝ → ℝ} {x : ℝ × ℝ} {z t ε : ℝ}
    (hD : NormalFrame.gramDet (SmallModes.coordDeriv SmallModes.dy F x)
      (SmallModes.coordDeriv SmallModes.dy (SmallModes.coordDeriv SmallModes.dy F) x) ≠ 0)
    (hframe : SmallModes.coordDeriv SmallModes.dy F x ⬝ᵥ e₁ x = 0 ∧
      SmallModes.coordDeriv SmallModes.dy (SmallModes.coordDeriv SmallModes.dy F) x ⬝ᵥ e₁ x = 0 ∧
      SmallModes.coordDeriv SmallModes.dy F x ⬝ᵥ e₂ x = 0 ∧
      SmallModes.coordDeriv SmallModes.dy (SmallModes.coordDeriv SmallModes.dy F) x ⬝ᵥ e₂ x = 0)
    (hclose : ‖GeometryPreservation.realBoundaryProfile W z x -
      GeometryPreservation.circularFamilyProfile Q
        (SmallModes.coordDeriv SmallModes.dx F) (SmallModes.coordDeriv SmallModes.dy F)
        (SmallModes.coordDeriv SmallModes.dy (SmallModes.coordDeriv SmallModes.dy F))
        R e₁ e₂ α SmallModes.dy (x, t)‖ < ε) :
    AnalyticFirstProfileEstimate F W x ε := by
  let X := SmallModes.coordDeriv SmallModes.dx F x
  let Y := SmallModes.coordDeriv SmallModes.dy F x
  let C := SmallModes.coordDeriv SmallModes.dy (SmallModes.coordDeriv SmallModes.dy F) x
  let lead := rawCircularLeading X Y C (e₁ x) (e₂ x) (R x) (α (x, t))
  have hx : ‖SmallModes.coordDeriv SmallModes.dx W x - lead‖ ≤ ε := by
    have hh := (norm_le_pi_norm _ 0).trans hclose.le
    change ‖SmallModes.coordDeriv SmallModes.dx W x -
      VelocityFrame.leadingTangent X Y C
        (R x • VelocityFrame.direction (e₁ x) (e₂ x) (α (x, t)))‖ ≤ ε at hh
    simpa only [lead, rawCircularLeading_eq_analytic] using hh
  have hy : ‖SmallModes.coordDeriv SmallModes.dy W x - Y‖ ≤ ε := by
    have hh := (norm_le_pi_norm _ 1).trans hclose.le
    change ‖SmallModes.coordDeriv SmallModes.dy W x - Y‖ ≤ ε at hh
    exact hh
  have hD' : rawGramDet Y C ≠ 0 := hD
  obtain ⟨hY, hC⟩ := rawCircularLeading_sub_perp hD'
    hframe.1 hframe.2.2.1 hframe.2.1 hframe.2.2.2 (R x) (α (x, t))
  refine ⟨lead - X, (dotProduct_comm _ _).trans hY,
    (dotProduct_comm _ _).trans hC, ?_, hy⟩
  have heq : SmallModes.coordDeriv SmallModes.dx W x - X - (lead - X) =
      SmallModes.coordDeriv SmallModes.dx W x - lead := by abel
  change ‖SmallModes.coordDeriv SmallModes.dx W x - X - (lead - X)‖ ≤ ε
  rw [heq]
  exact hx

/-- The certificate bounds the actual raw derivative operator, not only its entries. -/
theorem analytic_first_profile_raw_operator_bound
    {F W : (ℝ × ℝ) → RawVector} {x : ℝ × ℝ} {ε : ℝ}
    (hprofile : AnalyticFirstProfileEstimate F W x ε) :
    ∃ w : RawVector,
      w ⬝ᵥ fderiv ℝ F x (0, 1) = 0 ∧
      w ⬝ᵥ fderiv ℝ (fun q => fderiv ℝ F q (0, 1)) x (0, 1) = 0 ∧
      ‖fderiv ℝ W x - fderiv ℝ F x - coordinateTransverseMap w‖ ≤ 2 * ε := by
  obtain ⟨w, hY, hC, hx, hy⟩ := hprofile
  exact ⟨w, hY, hC, residual_bound_of_two_coordinate_profiles _ _ w hx hy⟩

/-- Conversion to Euclidean R4 costs a factor two. An exact correction of the
same approximant adds δ; the resulting transverse witness is still orthogonal
to the actual old y and yy derivatives. -/
theorem analytic_first_profile_corrected_space_operator_bound
    {F V : (ℝ × ℝ) → RawVector} {W : (ℝ × ℝ) → Space}
    {x : ℝ × ℝ} {ε δ : ℝ}
    (hF : DifferentiableAt ℝ F x) (hV : DifferentiableAt ℝ V x)
    (hprofile : AnalyticFirstProfileEstimate F V x ε)
    (hcorrection : ‖fderiv ℝ W x - fderiv ℝ (rawToSpace ∘ V) x‖ ≤ δ) :
    ∃ w : Space,
      inner ℝ w (rawToSpace (fderiv ℝ F x (0, 1))) = 0 ∧
      inner ℝ w (rawToSpace
        (fderiv ℝ (fun q => fderiv ℝ F q (0, 1)) x (0, 1))) = 0 ∧
      ‖fderiv ℝ W x - fderiv ℝ (rawToSpace ∘ F) x -
        coordinateTransverseMap w‖ ≤ 4 * ε + δ := by
  obtain ⟨w, hY, hC, hx, hy⟩ := hprofile
  have hFd := (rawToSpace.hasFDerivAt.comp x hF.hasFDerivAt).fderiv
  have hVd := (rawToSpace.hasFDerivAt.comp x hV.hasFDerivAt).fderiv
  have hx' : ‖fderiv ℝ (rawToSpace ∘ V) x (1, 0) -
      fderiv ℝ (rawToSpace ∘ F) x (1, 0) - rawToSpace w‖ ≤ 2 * ε := by
    rw [hFd, hVd]
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, map_sub] using
      (norm_rawToSpace_le _).trans (mul_le_mul_of_nonneg_left hx (by norm_num : (0 : ℝ) ≤ 2))
  have hy' : ‖fderiv ℝ (rawToSpace ∘ V) x (0, 1) -
      fderiv ℝ (rawToSpace ∘ F) x (0, 1)‖ ≤ 2 * ε := by
    rw [hFd, hVd]
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, map_sub] using
      (norm_rawToSpace_le _).trans (mul_le_mul_of_nonneg_left hy (by norm_num : (0 : ℝ) ≤ 2))
  refine ⟨rawToSpace w, rawToSpace_orthogonal hY, rawToSpace_orthogonal hC, ?_⟩
  simpa only [show (2 : ℝ) * (2 * ε) = 4 * ε by ring] using
    residual_bound_of_corrected_coordinate_profiles _ _ _ (rawToSpace w) hx' hy' hcorrection

end R4Embedding
