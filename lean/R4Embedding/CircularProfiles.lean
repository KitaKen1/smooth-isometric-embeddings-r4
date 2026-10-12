import R4Embedding.RawProfileAtlas

/-! The circular first profile is X - normalPart(Y,C,X) + R*direction.
This finite-coordinate algebra proves that its difference from X is in
the testing kernel. No unit-frame, nonzero-radius, or smooth phase choice
is needed for this particular implication. -/

noncomputable section

namespace R4Embedding

open scoped Matrix ContDiff

def rawGramDet (Y C : RawVector) : ℝ :=
  (Y ⬝ᵥ Y) * (C ⬝ᵥ C) - (Y ⬝ᵥ C) ^ 2

def rawNormalPart (Y C X : RawVector) : RawVector :=
  X - (((C ⬝ᵥ C) * (Y ⬝ᵥ X) - (Y ⬝ᵥ C) * (C ⬝ᵥ X)) /
    rawGramDet Y C) • Y -
    (((Y ⬝ᵥ Y) * (C ⬝ᵥ X) - (Y ⬝ᵥ C) * (Y ⬝ᵥ X)) /
    rawGramDet Y C) • C

def rawCircularLeading (X Y C e₁ e₂ : RawVector) (R α : ℝ) : RawVector :=
  X - rawNormalPart Y C X + R • (Real.cos α • e₁ + Real.sin α • e₂)

theorem rawNormalPart_perp (Y C X : RawVector) (hD : rawGramDet Y C ≠ 0) :
    Y ⬝ᵥ rawNormalPart Y C X = 0 ∧ C ⬝ᵥ rawNormalPart Y C X = 0 := by
  constructor
  · simp only [rawNormalPart, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    field_simp [hD]
    simp only [rawGramDet]
    ring
  · simp only [rawNormalPart, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      dotProduct_comm C Y]
    field_simp [hD]
    simp only [rawGramDet]
    ring

theorem rawCircularLeading_sub_perp {X Y C e₁ e₂ : RawVector}
    (hD : rawGramDet Y C ≠ 0)
    (hY₁ : Y ⬝ᵥ e₁ = 0) (hY₂ : Y ⬝ᵥ e₂ = 0)
    (hC₁ : C ⬝ᵥ e₁ = 0) (hC₂ : C ⬝ᵥ e₂ = 0) (R α : ℝ) :
    Y ⬝ᵥ (rawCircularLeading X Y C e₁ e₂ R α - X) = 0 ∧
    C ⬝ᵥ (rawCircularLeading X Y C e₁ e₂ R α - X) = 0 := by
  obtain ⟨hY, hC⟩ := rawNormalPart_perp Y C X hD
  simp [rawCircularLeading, dotProduct_sub, dotProduct_add, dotProduct_smul,
    hY, hC, hY₁, hY₂, hC₁, hC₂]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

/-- These are the first two entries of the circular profile. The phase and
frame may be chosen independently at each point. -/
def SmoothSurfaceProfileGeometry.HasCircularFirstProfiles {p : M}
    (data : SmoothSurfaceProfileGeometry M p) (r ε : ℝ) (f : M → Space) : Prop :=
  ∀ q ∈ Metric.ball (data.chart p) r, ∃ e₁ e₂ : RawVector, ∃ R α : ℝ,
    rawGramDet (rawToSpace.symm (data.v q)) (rawToSpace.symm (data.acc q)) ≠ 0 ∧
    rawToSpace.symm (data.v q) ⬝ᵥ e₁ = 0 ∧ rawToSpace.symm (data.v q) ⬝ᵥ e₂ = 0 ∧
    rawToSpace.symm (data.acc q) ⬝ᵥ e₁ = 0 ∧ rawToSpace.symm (data.acc q) ⬝ᵥ e₂ = 0 ∧
    ‖rawToSpace.symm (fderiv ℝ (f ∘ data.chart.symm) q (1, 0)) -
      rawCircularLeading (rawToSpace.symm (data.u q)) (rawToSpace.symm (data.v q))
        (rawToSpace.symm (data.acc q)) e₁ e₂ R α‖ ≤ ε ∧
    ‖rawToSpace.symm (fderiv ℝ (f ∘ data.chart.symm) q (0, 1)) -
      rawToSpace.symm (data.v q)‖ ≤ ε

theorem SmoothSurfaceProfileGeometry.HasCircularFirstProfiles.toRawFirstProfiles {p : M}
    {data : SmoothSurfaceProfileGeometry M p} {r ε : ℝ} {f : M → Space}
    (hf : data.HasCircularFirstProfiles r ε f) : data.HasRawFirstProfiles r ε f := by
  intro q hq
  obtain ⟨e₁, e₂, R, α, hD, hY₁, hY₂, hC₁, hC₂, hx, hy⟩ := hf q hq
  let X := rawToSpace.symm (data.u q)
  let Y := rawToSpace.symm (data.v q)
  let C := rawToSpace.symm (data.acc q)
  let lead := rawCircularLeading X Y C e₁ e₂ R α
  obtain ⟨hY, hC⟩ := rawCircularLeading_sub_perp hD hY₁ hY₂ hC₁ hC₂ R α
  refine ⟨lead - X, ?_, ?_, ?_, ?_⟩
  · change (lead - X) ⬝ᵥ Y = 0
    exact (dotProduct_comm _ _).trans hY
  · change (lead - X) ⬝ᵥ C = 0
    exact (dotProduct_comm _ _).trans hC
  · rw [map_sub]
    have he : rawToSpace.symm (fderiv ℝ (f ∘ data.chart.symm) q (1, 0)) -
        rawToSpace.symm (data.u q) - (lead - X) =
        rawToSpace.symm (fderiv ℝ (f ∘ data.chart.symm) q (1, 0)) - lead := by
      dsimp [X]
      abel
    rw [he]
    exact hx
  · simpa only [map_sub] using hy

theorem exists_isometric_embedding_of_circular_profile_construction [CompactSpace M]
    (g : SmoothMetric M) (data : ∀ p : M, SmoothSurfaceProfileGeometry M p)
    {F : M → Space} (hF : Continuous F) (hFinj : Function.Injective F)
    (hconstruct : ∀ (centers : Finset M) (r : M → ℝ) (ε η : ℝ),
      0 < ε → 0 < η →
      (∀ p, 0 < r p ∧ Metric.closedBall ((data p).chart p) (r p) ⊆ (data p).chart.target) →
      (∀ x, ∃ p ∈ centers, x ∈ chartBallPatch (data p).chart p (r p)) →
      ∃ f : M → Space, IsSmoothIsometricMap g f ∧
        (∀ p ∈ centers, (data p).HasCircularFirstProfiles (r p) ε f) ∧
        (∀ x, dist (f x) (F x) < η)) :
    ∃ f : M → Space, IsSmoothIsometricEmbedding g f := by
  apply exists_isometric_embedding_of_raw_profile_construction g data hF hFinj
  intro centers r ε η hε hη hr hcover
  obtain ⟨f, hf, hprofiles, hclose⟩ := hconstruct centers r ε η hε hη hr hcover
  exact ⟨f, hf, fun p hp => (hprofiles p hp).toRawFirstProfiles, hclose⟩

end R4Embedding
