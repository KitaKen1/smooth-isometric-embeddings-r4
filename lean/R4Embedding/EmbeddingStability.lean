import R4Embedding.OrdinaryProfiles

/-! C-one embedding preservation for the finite-point spherical preparation.
The new map need not share a fixed metric. Ordinary derivative closeness
bounds its derivative by the old local bound plus one; all radii and
tolerances precede the new map and any finite set of preparation points. -/

noncomputable section
namespace R4Embedding

open Set Manifold
open scoped ContDiff

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem SmoothSurfaceProfileGeometry.exists_radius_tolerance_of_derivative_close
    {F : M → Space} {p : M} (data : SmoothSurfaceProfileGeometry M p)
    (hu : data.u = coordinateSurfaceX (F ∘ data.chart.symm))
    (hv : data.v = coordinateSurfaceY (F ∘ data.chart.symm))
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hpU : data.chart p ∈ U) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧
      Metric.closedBall (data.chart p) r ⊆ data.chart.target ∩ U ∧
      ∀ W : M → Space, ContMDiff planeModel spaceModel ∞ W →
        (∀ q ∈ Metric.ball (data.chart p) r,
          ‖fderiv ℝ (W ∘ data.chart.symm) q - fderiv ℝ (F ∘ data.chart.symm) q‖ ≤ δ) →
        Set.InjOn W (chartBallPatch data.chart p r) := by
  let D := fun q => surfaceTangentMap (data.u q) (data.v q)
  have hDc : ContinuousAt D (data.chart p) :=
    surfaceTangentMap_continuousAt data.u_continuous data.v_continuous
  obtain ⟨rOld, hrOld, hold⟩ := exists_local_norm_bound hDc
  let B := ‖D (data.chart p)‖ + 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨rLocal, ε, hrLocal, hε, hlocal⟩ :=
    exists_injective_convex_patch_of_surface_profiles data.u data.v data.acc
      (data.chart p) data.u_continuous data.v_continuous data.acc_continuous
      data.tangent_injective data.gauss data.k_ne_zero data.normal_u data.normal_v hB
  obtain ⟨R, hR, htarget⟩ := Metric.mem_nhds_iff.mp
    ((data.chart.open_target.inter hU).mem_nhds ⟨data.chart.map_source data.mem_source, hpU⟩)
  let r := min (min rLocal rOld) (R / 2)
  have hr : 0 < r := lt_min (lt_min hrLocal hrOld) (half_pos hR)
  have hrR : r < R := (min_le_right _ _).trans_lt (half_lt_self hR)
  have hclosed : Metric.closedBall (data.chart p) r ⊆ data.chart.target ∩ U :=
    (Metric.closedBall_subset_ball hrR).trans htarget
  have hDf (q : ℝ × ℝ) : fderiv ℝ (F ∘ data.chart.symm) q = D q := by
    dsimp only [D]
    rw [hu, hv]
    exact (surfaceTangentMap_of_coordinate_derivative _).symm
  refine ⟨r, min ε 1, hr, lt_min hε zero_lt_one, hclosed, ?_⟩
  intro W hW hclose
  apply injOn_of_chartBallPatch data.chart p r
  apply hlocal (Metric.ball (data.chart p) r) (convex_ball _ _)
    (Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)))
    (W ∘ data.chart.symm) (fun q => fderiv ℝ (W ∘ data.chart.symm) q)
  · intro q hq
    have hqt := (hclosed (Metric.ball_subset_closedBall hq)).1
    have hs := coordinate_surface_contDiffAt hW data.chart data.smooth_inverse
      (data.chart.map_target hqt)
    rw [data.chart.right_inv hqt] at hs
    exact (hs.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  · intro q hq
    have hqo : q ∈ Metric.ball (data.chart p) rOld :=
      Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hq
    have hOld : ‖fderiv ℝ (F ∘ data.chart.symm) q‖ ≤ ‖D (data.chart p)‖ + 1 := by
      rw [hDf q]
      exact hold q hqo
    calc
      ‖fderiv ℝ (W ∘ data.chart.symm) q‖ =
          ‖(fderiv ℝ (W ∘ data.chart.symm) q - fderiv ℝ (F ∘ data.chart.symm) q) +
            fderiv ℝ (F ∘ data.chart.symm) q‖ := by rw [sub_add_cancel]
      _ ≤ ‖fderiv ℝ (W ∘ data.chart.symm) q - fderiv ℝ (F ∘ data.chart.symm) q‖ +
          ‖fderiv ℝ (F ∘ data.chart.symm) q‖ := norm_add_le _ _
      _ ≤ min ε 1 + (‖D (data.chart p)‖ + 1) := add_le_add (hclose q hq) hOld
      _ ≤ B := by dsimp [B]; linarith [min_le_right ε 1]
  · exact (coordinate_first_profiles_of_derivative_close data hu hv hclose).mono (min_le_left _ _)

theorem exists_closed_embedding_tolerance_of_derivative_close_in_open [CompactSpace M]
    {F : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (hFinj : Function.Injective F) (data : ∀ p : M, SmoothSurfaceProfileGeometry M p)
    (hu : ∀ p, (data p).u = coordinateSurfaceX (F ∘ (data p).chart.symm))
    (hv : ∀ p, (data p).v = coordinateSurfaceY (F ∘ (data p).chart.symm))
    (U : M → Set (ℝ × ℝ)) (hU : ∀ p, IsOpen (U p))
    (hpU : ∀ p, (data p).chart p ∈ U p) :
    ∃ centers : Finset M, ∃ r : M → ℝ, ∃ δ η : ℝ,
      0 < δ ∧ 0 < η ∧
      (∀ p, 0 < r p ∧ Metric.closedBall ((data p).chart p) (r p) ⊆
        (data p).chart.target ∩ U p) ∧
      (∀ x, ∃ p ∈ centers, x ∈ chartBallPatch (data p).chart p (r p)) ∧
      ∀ W : M → Space, ContMDiff planeModel spaceModel ∞ W →
        (∀ p ∈ centers, ∀ q ∈ Metric.ball ((data p).chart p) (r p),
          ‖fderiv ℝ (W ∘ (data p).chart.symm) q -
            fderiv ℝ (F ∘ (data p).chart.symm) q‖ ≤ δ) →
        (∀ x, dist (W x) (F x) < η) → Topology.IsClosedEmbedding W := by
  classical
  choose r δ₀ hr hδ₀ htarget hlocal using
    (fun p => (data p).exists_radius_tolerance_of_derivative_close (hu p) (hv p) (hU p) (hpU p))
  let patch := fun p => chartBallPatch (data p).chart p (r p)
  have hopen : ∀ p, IsOpen (patch p) := fun p => chartBallPatch_isOpen _ _ _
  have hself : ∀ p, p ∈ patch p := fun p =>
    mem_chartBallPatch (data p).chart (data p).mem_source (hr p)
  obtain ⟨centers, hcover⟩ := isCompact_univ.elim_finite_subcover patch hopen
    (fun p _ => mem_iUnion.mpr ⟨p, hself p⟩)
  obtain ⟨δ, hδ, hδbound⟩ := exists_positive_lower_bound_on_finset centers δ₀
    (fun p _ => hδ₀ p)
  let relation : Set (M × M) := ⋃ p ∈ centers, patch p ×ˢ patch p
  have hrelation : IsOpen relation := isOpen_biUnion (fun p _ => (hopen p).prod (hopen p))
  have hdiag : ∀ x, (x, x) ∈ relation := by
    intro x
    obtain ⟨p, hp⟩ := mem_iUnion.mp (hcover (Set.mem_univ x))
    obtain ⟨hpc, hpx⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨hpc, hpx, hpx⟩⟩
  obtain ⟨η, hη, hglobal⟩ := exists_embedding_tolerance hF.continuous hFinj hrelation hdiag
  refine ⟨centers, r, δ, η, hδ, hη, fun p => ⟨hr p, htarget p⟩, ?_, ?_⟩
  · intro x
    obtain ⟨p, hp⟩ := mem_iUnion.mp (hcover (Set.mem_univ x))
    obtain ⟨hpc, hpx⟩ := mem_iUnion.mp hp
    exact ⟨p, hpc, hpx⟩
  · intro W hW hclose hposition
    apply hglobal W hW.continuous _ hposition
    intro x y hxy heq
    obtain ⟨p, hp⟩ := mem_iUnion.mp hxy
    obtain ⟨hpc, hx, hy⟩ := mem_iUnion.mp hp
    exact hlocal p W hW (fun q hq => (hclose p hpc q hq).trans (hδbound p hpc)) hx hy heq

end R4Embedding
