import R4Embedding.ConvexPatch
import Mathlib.Analysis.Normed.Operator.Prod

/-! Concrete surface fields produce the testing operators and their
continuity. A nonzero Gauss coefficient supplies transversality. The old
derivative bound is obtained locally from continuity rather than assumed. -/

noncomputable section

namespace R4Embedding

section Bounds

variable {X G : Type*} [PseudoMetricSpace X] [NormedAddCommGroup G]

theorem exists_local_norm_bound {D : X → G} {p : X} (hD : ContinuousAt D p) :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ Metric.ball p r, ‖D q‖ ≤ ‖D p‖ + 1 := by
  obtain ⟨r, hr, hnear⟩ := Metric.continuousAt_iff.mp hD 1 zero_lt_one
  refine ⟨r, hr, ?_⟩
  intro q hq
  have h := hnear (show dist q p < r from hq)
  rw [dist_eq_norm] at h
  calc
    ‖D q‖ = ‖(D q - D p) + D p‖ := by rw [sub_add_cancel]
    _ ≤ ‖D q - D p‖ + ‖D p‖ := norm_add_le _ _
    _ ≤ ‖D p‖ + 1 := by linarith

end Bounds

section Surface

variable {X V : Type*} [TopologicalSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem surfaceTangentMap_continuousAt {u v : X → V} {p : X}
    (hu : ContinuousAt u p) (hv : ContinuousAt v p) :
    ContinuousAt (fun q => surfaceTangentMap (u q) (v q)) p := by
  exact (((ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) V)
    (ContinuousLinearMap.fst ℝ ℝ ℝ)).continuous.continuousAt.comp hu).add
    (((ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) V)
      (ContinuousLinearMap.snd ℝ ℝ ℝ)).continuous.continuousAt.comp hv)

theorem surfaceTestingMap_continuousAt {v acc : X → V} {p : X}
    (hv : ContinuousAt v p) (hacc : ContinuousAt acc p) :
    ContinuousAt (fun q => surfaceTestingMap (v q) (acc q)) p := by
  change ContinuousAt (fun q => (ContinuousLinearMap.prodₗᵢ ℝ)
    (innerSL ℝ (v q), innerSL ℝ (acc q))) p
  exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.continuousAt.comp_of_eq
    (((innerSL ℝ).continuous.continuousAt.comp hv).prodMk
      ((innerSL ℝ).continuous.continuousAt.comp hacc)) rfl

end Surface

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Local injectivity with the actual surface directions as inputs. Only the
new derivative bound M must be supplied (for example, by the fixed metric).
The old derivative bound, testing map, and fixed projection are constructed. -/
theorem exists_injective_convex_patch_of_surface_profiles
    (u v acc : (ℝ × ℝ) → V) (p : ℝ × ℝ)
    (hu : ContinuousAt u p) (hv : ContinuousAt v p) (hacc : ContinuousAt acc p)
    (hD : Function.Injective (surfaceTangentMap (u p) (v p)))
    {normal : V} {k l : ℝ}
    (hGauss : acc p = k • u p + l • v p + normal) (hk : k ≠ 0)
    (hnu : inner ℝ (u p) normal = 0) (hnv : inner ℝ (v p) normal = 0)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ r ε : ℝ, 0 < r ∧ 0 < ε ∧
      ∀ (s : Set (ℝ × ℝ)), Convex ℝ s → s ⊆ Metric.ball p r →
      ∀ (f : (ℝ × ℝ) → V) (df : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] V),
        (∀ q ∈ s, HasFDerivWithinAt f (df q) s q) →
        (∀ q ∈ s, ‖df q‖ ≤ M) →
        (∀ q ∈ s, ∃ w : V, inner ℝ w (v q) = 0 ∧ inner ℝ w (acc q) = 0 ∧
          ‖df q (1, 0) - u q - w‖ ≤ ε ∧ ‖df q (0, 1) - v q‖ ≤ ε) →
        Set.InjOn f s := by
  let D := fun q => surfaceTangentMap (u q) (v q)
  let A := fun q => surfaceTestingMap (v q) (acc q)
  have hcD : ContinuousAt D p := surfaceTangentMap_continuousAt hu hv
  have hcA : ContinuousAt A p := surfaceTestingMap_continuousAt hv hacc
  have hinj : Function.Injective ((A p).comp (D p)) :=
    surfaceTestingMap_tangent_injective hD hGauss hk hnu hnv
  obtain ⟨r₀, ε, hr₀, hε, hlocal⟩ := exists_injective_convex_patch_of_pointwise_profiles
    D A p hcD hcA hinj hM (show 0 ≤ ‖D p‖ + 1 by positivity)
  obtain ⟨r₁, hr₁, hbound⟩ := exists_local_norm_bound hcD
  refine ⟨min r₀ r₁, ε, lt_min hr₀ hr₁, hε, ?_⟩
  intro s hs hsub f df hf hdf hprofiles
  apply hlocal s hs (hsub.trans (Metric.ball_subset_ball (min_le_left _ _))) f df hf hdf
  · intro q hq
    exact hbound q (Metric.ball_subset_ball (min_le_right _ _) (hsub hq))
  · intro q hq
    obtain ⟨w, hwv, hwacc, hx, hy⟩ := hprofiles q hq
    refine ⟨w, ?_, ?_, ?_⟩
    · change surfaceTestingMap (v q) (acc q) w = 0
      rw [surfaceTestingMap_apply]
      exact Prod.ext ((real_inner_comm w (v q)).trans hwv)
        ((real_inner_comm w (acc q)).trans hwacc)
    · simpa only [D, surfaceTangentMap_apply, one_smul, zero_smul, add_zero] using hx
    · simpa only [D, surfaceTangentMap_apply, one_smul, zero_smul, zero_add] using hy

end R4Embedding
