import OAI.Geometry.SurfaceImmersion.Atlas.AtlasWeightedBounds

/-! Bounds for the actual outer localization on the supplied smoothing
atlas. Keeping this interface below the phase and polynomial correction
modules lets the coordinate estimates be checked independently.

All constants precede the future map and scale. The last theorem controls
the derivatives of the original maps in the actual atlas chart, wherever
the partition weight is nonzero. -/

noncomputable section
namespace R4Embedding

open Set Filter Manifold
open scoped ContDiff Topology BigOperators
open OAI.ClosedSurfaceR4 OAI.ClosedSurfaceR4.FiniteOrderSmoothing
open OAI.ClosedSurfaceR4.JetPolynomial

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [CompactSpace M] in
theorem analytic_outer_localize_restore (A : SmoothingAtlas M)
    (i j : A.centers) (f : JetPolynomial.Base → V) :
    localize (i : M) (A.outer i) (restore (j : M) (A.outer j) f) =
      fun x => localize (i : M) (A.outer i) (A.outer j) x •
        f (transition (i : M) (j : M) x) := by
  funext x
  by_cases hi : x ∈ (chart (i : M)).target
  · by_cases hj : (chart (i : M)).symm x ∈ (chart (j : M)).source
    · simp only [localize, restore, indicator_of_mem hi, indicator_of_mem hj]
      rw [smul_smul]
      rfl
    · have hz : A.outer j ((chart (i : M)).symm x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hj (A.outer_support j h))
      simp only [localize, restore, indicator_of_mem hi, indicator_of_notMem hj,
        hz, smul_zero, zero_smul]
  · simp only [localize, indicator_of_notMem hi, zero_smul]

theorem analytic_outer_localize_restore_bound (A : SmoothingAtlas M)
    (i j : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : JetPolynomial.Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedEstimates.WeightedBound univ s m C f →
      WeightedEstimates.WeightedBound univ s m (D * C)
        (localize (i : M) (A.outer i) (restore (j : M) (A.outer j) f)) := by
  let K := (chart (i : M)) '' (tsupport (A.outer i) ∩ tsupport (A.outer j))
  have hK : IsCompact K :=
    ((isClosed_tsupport _).inter (isClosed_tsupport _)).isCompact.image_of_continuousOn
      ((chart (i : M)).continuousOn.mono (fun _ h => A.outer_support i h.1))
  have hKO : K ⊆ (transition (i : M) (j : M)).source := by
    rintro x ⟨p, hp, rfl⟩
    refine ⟨(chart (i : M)).map_source (A.outer_support i hp.1), ?_⟩
    change (chart (i : M)).symm (chart (i : M) p) ∈ (chart (j : M)).source
    rw [(chart (i : M)).left_inv (A.outer_support i hp.1)]
    exact A.outer_support j hp.2
  obtain ⟨D, hD, hd⟩ := compact_localized_composition_bound (V := V)
    (transition (i : M) (j : M)).open_source hK hKO
    (localize_smooth (i : M) (A.outer_smooth i) (A.outer_support i) (A.outer_smooth j))
    (localize_tsupport_inter (i : M) (A.outer_support i) (A.outer j))
    (transition_smooth (i : M) (j : M)) m
  refine ⟨D, hD, ?_⟩
  intro f s C hs hs1 hC hf hb
  rw [analytic_outer_localize_restore A]
  exact hd f s C hs hs1 hC hf hb

theorem analytic_outer_read_weighted_bound (A : SmoothingAtlas M)
    (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      A.WeightedBound s m C F →
      WeightedEstimates.WeightedBound univ s m (D * C)
        (localize (i : M) (A.outer i) F) := by
  classical
  choose D hD hd using fun j : A.centers =>
    analytic_outer_localize_restore_bound (V := V) A i j m
  refine ⟨∑ j : A.centers, D j, Finset.sum_nonneg (fun j _ => hD j), ?_⟩
  intro F s C hs hs1 hC hF hb
  have he : localize (i : M) (A.outer i) F = fun x => ∑ j : A.centers,
      localize (i : M) (A.outer i)
        (restore (j : M) (A.outer j) (localize (j : M) (A.weight j) F)) x := by
    conv_lhs => rw [← A.sum_restore_localize F]
    exact localize_sum Finset.univ _ _ _
  rw [he, Finset.sum_mul]
  apply WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hs.le
  · intro j _
    exact (localize_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
      (restore_smooth (j : M) (A.outer_smooth j) (A.outer_support j)
        (localize_smooth (j : M) (A.weight_smooth j) (A.weight_support j) hF))).contDiffOn
  · intro j _
    exact hd j _ s C hs hs1 hC
      (localize_smooth (j : M) (A.weight_smooth j) (A.weight_support j) hF) (hb j)

omit [CompactSpace M] in
theorem analytic_outer_read_germ (A : SmoothingAtlas M) (i : A.centers)
    (F : M → V) {x : JetPolynomial.Base} (hx : x ∈ (chart (i : M)).target)
    (hw : A.weight i ((chart (i : M)).symm x) ≠ 0) :
    localize (i : M) (A.outer i) F =ᶠ[𝓝 x] F ∘ (chart (i : M)).symm := by
  have hn : ∀ᶠ p in 𝓝 ((chart (i : M)).symm x), A.weight i p ≠ 0 :=
    (isOpen_ne.preimage (A.weight_smooth i).continuous).mem_nhds hw
  have hc := (chart (i : M)).continuousAt_symm hx
  have htarget : ∀ᶠ y in 𝓝 x, y ∈ (chart (i : M)).target :=
    (chart (i : M)).open_target.mem_nhds hx
  filter_upwards [hc.eventually hn, htarget] with y hy ht
  rw [localize, indicator_of_mem ht,
    A.outer_one i _ (subset_tsupport (A.weight i) hy), one_pow, one_smul]
  rfl

theorem analytic_outer_read_derivative_difference_bound (A : SmoothingAtlas M)
    (i : A.centers) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F W : M → V),
      ContMDiff planeModel 𝓘(ℝ,V) ∞ F → ContMDiff planeModel 𝓘(ℝ,V) ∞ W →
      ∀ C : ℝ, 0 ≤ C → A.WeightedBound 1 1 C (W - F) → ∀ x : JetPolynomial.Base,
        ‖fderiv ℝ (localize (i : M) (A.outer i) W) x -
          fderiv ℝ (localize (i : M) (A.outer i) F) x‖ ≤ D * C := by
  obtain ⟨D, hD, hd⟩ := analytic_outer_read_weighted_bound (V := V) A i 1
  refine ⟨D, hD, ?_⟩
  intro F W hF hW C hC hclose x
  have hb := hd (W - F) 1 C zero_lt_one le_rfl hC (hW.sub hF) hclose
  have hh := (hb.fderivWithin uniqueDiffOn_univ zero_lt_one).norm_le (mem_univ x)
  have he : localize (i : M) (A.outer i) (W - F) =
      localize (i : M) (A.outer i) W - localize (i : M) (A.outer i) F := by
    funext y
    by_cases hy : y ∈ (chart (i : M)).target <;>
      simp [localize, hy, smul_sub]
  change ‖fderivWithin ℝ (localize (i : M) (A.outer i) (W - F)) univ x‖ ≤ _ at hh
  rw [he, fderivWithin_univ,
    fderiv_sub ((localize_smooth (i : M) (A.outer_smooth i) (A.outer_support i) hW).differentiable
      (by simp) x)
      ((localize_smooth (i : M) (A.outer_smooth i) (A.outer_support i) hF).differentiable
        (by simp) x)] at hh
  simpa only [div_one] using hh

/-- The bound is for the actual same input and output maps in the original
atlas coordinate, without replacing their smooth structure. -/
theorem analytic_weighted_chart_derivative_difference_bound (A : SmoothingAtlas M)
    (i : A.centers) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F W : M → V),
      ContMDiff planeModel 𝓘(ℝ,V) ∞ F → ContMDiff planeModel 𝓘(ℝ,V) ∞ W →
      ∀ C : ℝ, 0 ≤ C → A.WeightedBound 1 1 C (W - F) →
      ∀ x : JetPolynomial.Base, x ∈ (chart (i : M)).target →
        A.weight i ((chart (i : M)).symm x) ≠ 0 →
        ‖fderiv ℝ (W ∘ (chart (i : M)).symm) x -
          fderiv ℝ (F ∘ (chart (i : M)).symm) x‖ ≤ D * C := by
  obtain ⟨D, hD, hd⟩ := analytic_outer_read_derivative_difference_bound (V := V) A i
  refine ⟨D, hD, ?_⟩
  intro F W hF hW C hC hclose x hx hw
  have hFread := (analytic_outer_read_germ A i F hx hw).fderiv_eq (𝕜 := ℝ)
  have hWread := (analytic_outer_read_germ A i W hx hw).fderiv_eq (𝕜 := ℝ)
  have hb := hd F W hF hW C hC hclose x
  rwa [hFread, hWread] at hb

end R4Embedding
