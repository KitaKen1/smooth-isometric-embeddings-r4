import R4Embedding.PrimitiveInjectivity

/-! A chart may require a smaller domain than the initially selected ball.
The radius and tolerances below work for every convex subset of that ball,
with derivative hypotheses only on that subset. -/

noncomputable section

namespace R4Embedding

section General

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem exists_injective_convex_patch_of_transverse_perturbation
    (D : E → E →L[ℝ] V) (P : E → V →L[ℝ] V) (L : V →L[ℝ] E) (p : E)
    (hD : ContinuousAt D p) (hP : ContinuousAt P p)
    (hleft : L.comp (D p) = ContinuousLinearMap.id ℝ E)
    (hkill : L.comp (P p) = 0) {B : ℝ} (hB : 0 ≤ B) :
    ∃ r ρ : ℝ, 0 < r ∧ 0 < ρ ∧
      ∀ (s : Set E), Convex ℝ s → s ⊆ Metric.ball p r →
      ∀ (f : E → V) (df W : E → E →L[ℝ] V),
        (∀ q ∈ s, HasFDerivWithinAt f (df q) s q) →
        (∀ q ∈ s, (P q).comp (W q) = W q) →
        (∀ q ∈ s, ‖W q‖ ≤ B) →
        (∀ q ∈ s, ‖df q - D q - W q‖ ≤ ρ) → Set.InjOn f s := by
  obtain ⟨η, hη, hηbudget⟩ := exists_positive_scaled_tolerance
    (mul_nonneg (norm_nonneg L) hB) (show (0 : ℝ) < 1 / 4 by norm_num)
  obtain ⟨ρ, hρ, hρbudget⟩ := exists_positive_scaled_tolerance
    (norm_nonneg L) (show (0 : ℝ) < 1 / 4 by norm_num)
  obtain ⟨r, hr, hbounds⟩ := exists_local_projection_bounds D P L p hD hP hleft hη
  refine ⟨r, ρ, hr, hρ, ?_⟩
  intro s hs hsub f df W hf hrange hW hresidual
  apply injOn_of_projected_derivative_decomposition
    (old := D) (transverse := W) (residual := fun q => df q - D q - W q)
    L (a := 1 / 4) (b := 1 / 4) (c := 1 / 4) hs hf
  · intro q _
    abel
  · intro q hq
    exact (hbounds q (hsub hq)).1
  · intro q hq
    have h := projected_transverse_bound_of_bounds L (P q) (P p) (W q)
      (hrange q hq) hkill (hbounds q (hsub hq)).2 (hW q hq)
    exact h.trans (by nlinarith [hηbudget])
  · intro q hq
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (hresidual q hq) (norm_nonneg L))).trans hρbudget
  · norm_num

theorem exists_injective_convex_patch_of_testing_transversality [FiniteDimensional ℝ E]
    (D : E → E →L[ℝ] V) (A : E → V →L[ℝ] E) (p : E)
    (hD : ContinuousAt D p) (hA : ContinuousAt A p)
    (hinj : Function.Injective ((A p).comp (D p))) {B : ℝ} (hB : 0 ≤ B) :
    ∃ r ρ : ℝ, 0 < r ∧ 0 < ρ ∧
      ∀ (s : Set E), Convex ℝ s → s ⊆ Metric.ball p r →
      ∀ (f : E → V) (df W : E → E →L[ℝ] V),
        (∀ q ∈ s, HasFDerivWithinAt f (df q) s q) →
        (∀ q ∈ s, (A q).comp (W q) = 0) →
        (∀ q ∈ s, ‖W q‖ ≤ B) →
        (∀ q ∈ s, ‖df q - D q - W q‖ ≤ ρ) → Set.InjOn f s := by
  have hinv := testing_comp_isInvertible (D p) (A p) hinj
  have hleft := testingLeftProjection_left (D p) (A p) hinv
  have hP := testingComplementProjection_continuousAt D A p hD hA hinv
  have hkill : (testingLeftProjection (D p) (A p)).comp
      (testingComplementProjection (D p) (A p)) = 0 :=
    complementProjection_killed _ _ hleft
  obtain ⟨r, ρ, hr, hρ, hall⟩ := exists_injective_convex_patch_of_transverse_perturbation D
    (fun q => testingComplementProjection (D q) (A q))
    (testingLeftProjection (D p) (A p)) p hD hP hleft hkill hB
  refine ⟨r, ρ, hr, hρ, ?_⟩
  intro s hs hsub f df W hf hW hbound hresidual
  exact hall s hs hsub f df W hf
    (fun q hq => testingComplementProjection_fixes (D q) (A q) (W q) (hW q hq))
    hbound hresidual

end General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem exists_injective_convex_patch_of_pointwise_profiles
    (D : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] V)
    (A : (ℝ × ℝ) → V →L[ℝ] (ℝ × ℝ)) (p : ℝ × ℝ)
    (hD : ContinuousAt D p) (hA : ContinuousAt A p)
    (hinj : Function.Injective ((A p).comp (D p)))
    {M M₀ : ℝ} (hM : 0 ≤ M) (hM₀ : 0 ≤ M₀) :
    ∃ r ε : ℝ, 0 < r ∧ 0 < ε ∧
      ∀ (s : Set (ℝ × ℝ)), Convex ℝ s → s ⊆ Metric.ball p r →
      ∀ (f : (ℝ × ℝ) → V) (df : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] V),
        (∀ q ∈ s, HasFDerivWithinAt f (df q) s q) →
        (∀ q ∈ s, ‖df q‖ ≤ M) → (∀ q ∈ s, ‖D q‖ ≤ M₀) →
        (∀ q ∈ s, ∃ w : V, A q w = 0 ∧
          ‖df q (1, 0) - D q (1, 0) - w‖ ≤ ε ∧
          ‖df q (0, 1) - D q (0, 1)‖ ≤ ε) → Set.InjOn f s := by
  classical
  obtain ⟨r, ρ, hr, hρ, hall⟩ := exists_injective_convex_patch_of_testing_transversality
    D A p hD hA hinj (B := M + M₀ + 1) (by linarith)
  let ε := min ρ 1 / 2
  have hε : 0 < ε := half_pos (lt_min hρ zero_lt_one)
  have hερ : 2 * ε ≤ ρ := by dsimp [ε]; linarith [min_le_left ρ 1]
  have hεone : 2 * ε ≤ 1 := by dsimp [ε]; linarith [min_le_right ρ 1]
  refine ⟨r, ε, hr, hε, ?_⟩
  intro s hs hsub f df hf hdf hold hprofiles
  have hexists : ∀ q, ∃ w : V, q ∈ s → A q w = 0 ∧
      ‖df q (1, 0) - D q (1, 0) - w‖ ≤ ε ∧
      ‖df q (0, 1) - D q (0, 1)‖ ≤ ε := by
    intro q
    by_cases hq : q ∈ s
    · obtain ⟨w, hw⟩ := hprofiles q hq
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h => False.elim (hq h)⟩
  choose w hw using hexists
  have hresidual (q) (hq : q ∈ s) :
      ‖df q - D q - coordinateTransverseMap (w q)‖ ≤ 2 * ε :=
    residual_bound_of_two_coordinate_profiles (df q) (D q) (w q)
      (hw q hq).2.1 (hw q hq).2.2
  apply hall s hs hsub f df (fun q => coordinateTransverseMap (w q)) hf
  · intro q hq
    exact coordinateTransverseMap_killed (A q) (hw q hq).1
  · intro q hq
    exact (transverse_norm_bound_of_exact_derivative (df q) (D q) _
      (hdf q hq) (hold q hq) (hresidual q hq)).trans (by linarith)
  · intro q hq
    exact (hresidual q hq).trans hερ

end R4Embedding
