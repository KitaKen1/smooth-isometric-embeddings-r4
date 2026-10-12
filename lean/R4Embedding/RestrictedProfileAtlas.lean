import R4Embedding.RawProfileAtlas

/-! Choose each chart ball inside a prescribed open region before selecting
the output. This allows active phase charts and ordinary exterior charts to
share the finite atlas without asking for estimates across their boundaries.
-/

noncomputable section
namespace R4Embedding

open Bundle Manifold Set
open scoped ContDiff

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem SmoothSurfaceProfileGeometry.exists_radius_tolerance_in_open {p : M}
    (g : SmoothMetric M) (data : SmoothSurfaceProfileGeometry M p)
    (D : Set (ℝ × ℝ)) (hD : IsOpen D) (hpD : data.chart p ∈ D) :
    ∃ r ε : ℝ, 0 < r ∧ 0 < ε ∧
      Metric.closedBall (data.chart p) r ⊆ data.chart.target ∩ D ∧
      ∀ f : M → Space, IsSmoothIsometricMap g f →
        data.HasFirstProfiles r ε f → Set.InjOn f (chartBallPatch data.chart p r) := by
  obtain ⟨R, hR, htarget⟩ := Metric.mem_nhds_iff.mp
    ((data.chart.open_target.inter hD).mem_nhds
      ⟨data.chart.map_source data.mem_source, hpD⟩)
  let R₀ := R / 2
  have hR₀ : 0 < R₀ := half_pos hR
  have hclosed : Metric.closedBall (data.chart p) R₀ ⊆ data.chart.target ∩ D :=
    (Metric.closedBall_subset_ball (half_lt_self hR)).trans htarget
  have hclosedTarget : Metric.closedBall (data.chart p) R₀ ⊆ data.chart.target :=
    fun _ hx => (hclosed hx).1
  obtain ⟨B, hB, hbound⟩ := exists_uniform_isometric_derivative_bound_on_smooth_coordinates
    g data.chart.symm data.chart.open_target data.smooth_inverse
    (isCompact_closedBall (data.chart p) R₀) hclosedTarget
  obtain ⟨r₁, ε, hr₁, hε, hlocal⟩ := exists_injective_convex_patch_of_surface_profiles
    data.u data.v data.acc (data.chart p) data.u_continuous data.v_continuous
    data.acc_continuous data.tangent_injective data.gauss data.k_ne_zero
    data.normal_u data.normal_v hB
  let r := min r₁ R₀
  have hr : 0 < r := lt_min hr₁ hR₀
  have hsmall : Metric.ball (data.chart p) r ⊆ Metric.closedBall (data.chart p) R₀ :=
    (Metric.ball_subset_ball (min_le_right _ _)).trans Metric.ball_subset_closedBall
  refine ⟨r, ε, hr, hε,
    (Metric.closedBall_subset_closedBall (min_le_right _ _)).trans hclosed, ?_⟩
  intro f hf hprofiles
  apply injOn_of_chartBallPatch data.chart p r
  apply hlocal (Metric.ball (data.chart p) r) (convex_ball _ _)
    (Metric.ball_subset_ball (min_le_left _ _)) (f ∘ data.chart.symm)
    (fun q => fderiv ℝ (f ∘ data.chart.symm) q)
  · intro q hq
    have hc := ((data.smooth_inverse.mdifferentiableOn (by simp)) q
      (hclosedTarget (hsmall hq))).mdifferentiableAt
      (data.chart.open_target.mem_nhds (hclosedTarget (hsmall hq)))
    simpa only [hf.fderiv_comp_coordinate hc] using
      (hf.hasFDerivAt_comp_coordinate hc).hasFDerivWithinAt
  · intro q hq
    exact hbound f hf q (hsmall hq)
  · exact hprofiles

/-- Region restrictions, finite cover, and both tolerances are all fixed
before the future metric-preserving map. -/
theorem exists_closed_embedding_tolerance_of_metric_profiles_in_open [CompactSpace M]
    (g : SmoothMetric M) (data : ∀ p : M, SmoothSurfaceProfileGeometry M p)
    (D : M → Set (ℝ × ℝ)) (hD : ∀ p, IsOpen (D p))
    (hpD : ∀ p, (data p).chart p ∈ D p)
    {F : M → Space} (hF : Continuous F) (hFinj : Function.Injective F) :
    ∃ centers : Finset M, ∃ r : M → ℝ, ∃ ε η : ℝ,
      0 < ε ∧ 0 < η ∧
      (∀ p, 0 < r p ∧ Metric.closedBall ((data p).chart p) (r p) ⊆
        (data p).chart.target ∩ D p) ∧
      (∀ x, ∃ p ∈ centers, x ∈ chartBallPatch (data p).chart p (r p)) ∧
      ∀ f : M → Space, IsSmoothIsometricMap g f →
        (∀ p ∈ centers, (data p).HasFirstProfiles (r p) ε f) →
        (∀ x, dist (f x) (F x) < η) → Topology.IsClosedEmbedding f := by
  classical
  choose r ε₀ hr hε₀ htarget hlocal using
    (fun p => (data p).exists_radius_tolerance_in_open g (D p) (hD p) (hpD p))
  let patch := fun p => chartBallPatch (data p).chart p (r p)
  have hopen : ∀ p, IsOpen (patch p) := fun p => chartBallPatch_isOpen _ _ _
  have hself : ∀ p, p ∈ patch p := fun p => mem_chartBallPatch (data p).chart
    (data p).mem_source (hr p)
  obtain ⟨centers, hcover⟩ := isCompact_univ.elim_finite_subcover patch hopen
    (fun p _ => mem_iUnion.mpr ⟨p, hself p⟩)
  obtain ⟨ε, hε, hεbound⟩ := exists_positive_lower_bound_on_finset centers ε₀
    (fun p _ => hε₀ p)
  let U : Set (M × M) := ⋃ p ∈ centers, patch p ×ˢ patch p
  have hU : IsOpen U := isOpen_biUnion (fun p _ => (hopen p).prod (hopen p))
  have hdiag : ∀ x, (x, x) ∈ U := by
    intro x
    obtain ⟨p, hp⟩ := mem_iUnion.mp (hcover (Set.mem_univ x))
    obtain ⟨hpc, hpx⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨hpc, hpx, hpx⟩⟩
  obtain ⟨η, hη, hglobal⟩ := exists_embedding_tolerance hF hFinj hU hdiag
  refine ⟨centers, r, ε, η, hε, hη, fun p => ⟨hr p, htarget p⟩, ?_, ?_⟩
  · intro x
    obtain ⟨p, hp⟩ := mem_iUnion.mp (hcover (Set.mem_univ x))
    obtain ⟨hpc, hpx⟩ := mem_iUnion.mp hp
    exact ⟨p, hpc, hpx⟩
  · intro f hf hprofiles hclose
    apply hglobal f hf.1.continuous _ hclose
    intro x y hxy heq
    obtain ⟨p, hp⟩ := mem_iUnion.mp hxy
    obtain ⟨hpc, hx, hy⟩ := mem_iUnion.mp hp
    exact hlocal p f hf ((hprofiles p hpc).mono (hεbound p hpc)) hx hy heq

theorem exists_closed_embedding_tolerance_of_raw_metric_profiles_in_open [CompactSpace M]
    (g : SmoothMetric M) (data : ∀ p : M, SmoothSurfaceProfileGeometry M p)
    (D : M → Set (ℝ × ℝ)) (hD : ∀ p, IsOpen (D p))
    (hpD : ∀ p, (data p).chart p ∈ D p)
    {F : M → Space} (hF : Continuous F) (hFinj : Function.Injective F) :
    ∃ centers : Finset M, ∃ r : M → ℝ, ∃ ε η : ℝ,
      0 < ε ∧ 0 < η ∧
      (∀ p, 0 < r p ∧ Metric.closedBall ((data p).chart p) (r p) ⊆
        (data p).chart.target ∩ D p) ∧
      (∀ x, ∃ p ∈ centers, x ∈ chartBallPatch (data p).chart p (r p)) ∧
      ∀ f : M → Space, IsSmoothIsometricMap g f →
        (∀ p ∈ centers, (data p).HasRawFirstProfiles (r p) ε f) →
        (∀ x, dist (f x) (F x) < η) → Topology.IsClosedEmbedding f := by
  obtain ⟨centers,r,ε,η,hε,hη,hr,hcover,htol⟩ :=
    exists_closed_embedding_tolerance_of_metric_profiles_in_open g data D hD hpD hF hFinj
  refine ⟨centers,r,ε / 2,η,half_pos hε,hη,hr,hcover,?_⟩
  intro f hf hprofiles hclose
  apply htol f hf _ hclose
  intro p hp
  simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using
    (hprofiles p hp).toFirstProfiles

end R4Embedding
