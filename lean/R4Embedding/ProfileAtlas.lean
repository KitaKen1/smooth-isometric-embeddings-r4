import R4Embedding.SurfaceProfiles
import R4Embedding.GlobalInjectivity
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! Genuine coordinate charts transfer the surface-profile injectivity
argument to a compact space. Compactness selects finitely many small chart
balls and a common profile tolerance before the perturbed map is chosen.
The input profile condition does not contain injectivity of that map. -/

noncomputable section

namespace R4Embedding

open Set

variable {X V : Type*} [TopologicalSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def chartBallPatch (e : OpenPartialHomeomorph X (ℝ × ℝ)) (p : X) (r : ℝ) : Set X :=
  e.source ∩ e ⁻¹' Metric.ball (e p) r

theorem chartBallPatch_isOpen (e : OpenPartialHomeomorph X (ℝ × ℝ)) (p : X) (r : ℝ) :
    IsOpen (chartBallPatch e p r) :=
  e.continuousOn.isOpen_inter_preimage e.open_source Metric.isOpen_ball

theorem mem_chartBallPatch (e : OpenPartialHomeomorph X (ℝ × ℝ)) {p : X} {r : ℝ}
    (hp : p ∈ e.source) (hr : 0 < r) : p ∈ chartBallPatch e p r :=
  ⟨hp, Metric.mem_ball_self hr⟩

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] in
theorem injOn_of_chartBallPatch (e : OpenPartialHomeomorph X (ℝ × ℝ)) (p : X) (r : ℝ)
    {f : X → V} (hf : Set.InjOn (f ∘ e.symm) (Metric.ball (e p) r)) :
    Set.InjOn f (chartBallPatch e p r) := by
  intro x hx y hy hxy
  apply e.injOn hx.1 hy.1
  apply hf hx.2 hy.2
  simpa only [Function.comp_apply, e.left_inv hx.1, e.left_inv hy.1] using hxy

/-- A common positive tolerance exists even for an empty finite set. -/
theorem exists_positive_lower_bound_on_finset {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) : ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ s, ε ≤ a i := by
  classical
  revert ha
  induction s using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s hi ih =>
    intro ha
    obtain ⟨ε, hε, hbound⟩ := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
    refine ⟨min (a i) ε, lt_min (ha i (Finset.mem_insert_self _ _)) hε, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hbound j hj)

/-- Geometry of the old surface, without any bound on a future output. -/
structure SurfaceProfileGeometry (X V : Type*) [TopologicalSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] (p : X) where
  chart : OpenPartialHomeomorph X (ℝ × ℝ)
  mem_source : p ∈ chart.source
  u : (ℝ × ℝ) → V
  v : (ℝ × ℝ) → V
  acc : (ℝ × ℝ) → V
  u_continuous : ContinuousAt u (chart p)
  v_continuous : ContinuousAt v (chart p)
  acc_continuous : ContinuousAt acc (chart p)
  tangent_injective : Function.Injective (surfaceTangentMap (u (chart p)) (v (chart p)))
  normal : V
  k : ℝ
  l : ℝ
  gauss : acc (chart p) = k • u (chart p) + l • v (chart p) + normal
  k_ne_zero : k ≠ 0
  normal_u : inner ℝ (u (chart p)) normal = 0
  normal_v : inner ℝ (v (chart p)) normal = 0

/-- The general profile theorem also accepts an independently supplied
bound. For smooth metric-preserving outputs, SmoothProfileAtlas derives it. -/
structure SurfaceProfileChartData (X V : Type*) [TopologicalSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] (p : X)
    extends SurfaceProfileGeometry X V p where
  new_bound : ℝ
  new_bound_nonneg : 0 ≤ new_bound

/-- All estimates refer to the same coordinate representation of f. -/
def SurfaceProfileChartData.HasProfiles {p : X} (data : SurfaceProfileChartData X V p)
    (r ε : ℝ) (f : X → V) : Prop :=
  ∃ df : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] V,
    (∀ q ∈ Metric.ball (data.chart p) r,
      HasFDerivWithinAt (f ∘ data.chart.symm) (df q) (Metric.ball (data.chart p) r) q) ∧
    (∀ q ∈ Metric.ball (data.chart p) r, ‖df q‖ ≤ data.new_bound) ∧
    ∀ q ∈ Metric.ball (data.chart p) r, ∃ w : V,
      inner ℝ w (data.v q) = 0 ∧ inner ℝ w (data.acc q) = 0 ∧
      ‖df q (1, 0) - data.u q - w‖ ≤ ε ∧ ‖df q (0, 1) - data.v q‖ ≤ ε

theorem SurfaceProfileChartData.HasProfiles.mono {p : X}
    {data : SurfaceProfileChartData X V p} {r ε ε' : ℝ} {f : X → V}
    (hf : data.HasProfiles r ε f) (hε : ε ≤ ε') : data.HasProfiles r ε' f := by
  obtain ⟨df, hderiv, hbound, hprofiles⟩ := hf
  refine ⟨df, hderiv, hbound, ?_⟩
  intro q hq
  obtain ⟨w, hwv, hwacc, hx, hy⟩ := hprofiles q hq
  exact ⟨w, hwv, hwacc, hx.trans hε, hy.trans hε⟩

theorem SurfaceProfileChartData.exists_radius_tolerance {p : X}
    (data : SurfaceProfileChartData X V p) :
    ∃ r ε : ℝ, 0 < r ∧ 0 < ε ∧
      Metric.closedBall (data.chart p) r ⊆ data.chart.target ∧
      ∀ f : X → V, data.HasProfiles r ε f →
        Set.InjOn f (chartBallPatch data.chart p r) := by
  obtain ⟨r₀, ε, hr₀, hε, hlocal⟩ := exists_injective_convex_patch_of_surface_profiles
    data.u data.v data.acc (data.chart p) data.u_continuous data.v_continuous
    data.acc_continuous data.tangent_injective data.gauss data.k_ne_zero data.normal_u
    data.normal_v data.new_bound_nonneg
  obtain ⟨r₁, hr₁, htarget⟩ := Metric.mem_nhds_iff.mp
    (data.chart.open_target.mem_nhds (data.chart.map_source data.mem_source))
  let r := min r₀ (r₁ / 2)
  have hr : 0 < r := lt_min hr₀ (half_pos hr₁)
  have hsmall : r < r₁ := (min_le_right _ _).trans_lt (half_lt_self hr₁)
  refine ⟨r, ε, hr, hε, (Metric.closedBall_subset_ball hsmall).trans htarget, ?_⟩
  intro f hf
  obtain ⟨df, hderiv, hbound, hprofiles⟩ := hf
  apply injOn_of_chartBallPatch data.chart p r
  exact hlocal (Metric.ball (data.chart p) r) (convex_ball _ _)
    (Metric.ball_subset_ball (min_le_left _ _)) (f ∘ data.chart.symm) df
    hderiv hbound hprofiles

/-- Finitely many actual charts and two scalar tolerances suffice. Their
choice precedes f. No local or global injectivity is assumed for f. -/
theorem exists_closed_embedding_tolerance_of_surface_profile_charts [CompactSpace X]
    (data : ∀ p : X, SurfaceProfileChartData X V p)
    {F : X → V} (hF : Continuous F) (hFinj : Function.Injective F) :
    ∃ centers : Finset X, ∃ r : X → ℝ, ∃ ε η : ℝ,
      0 < ε ∧ 0 < η ∧
      (∀ p, 0 < r p ∧ Metric.closedBall ((data p).chart p) (r p) ⊆ (data p).chart.target) ∧
      (∀ x, ∃ p ∈ centers, x ∈ chartBallPatch (data p).chart p (r p)) ∧
      ∀ f : X → V, Continuous f →
        (∀ p ∈ centers, (data p).HasProfiles (r p) ε f) →
        (∀ x, dist (f x) (F x) < η) → Topology.IsClosedEmbedding f := by
  classical
  choose r ε₀ hr hε₀ htarget hlocal using
    (fun p => (data p).exists_radius_tolerance)
  let patch := fun p => chartBallPatch (data p).chart p (r p)
  have hopen : ∀ p, IsOpen (patch p) := fun p => chartBallPatch_isOpen _ _ _
  have hself : ∀ p, p ∈ patch p := fun p => mem_chartBallPatch (data p).chart
    (data p).mem_source (hr p)
  obtain ⟨centers, hcover⟩ := isCompact_univ.elim_finite_subcover patch hopen
    (fun p _ => mem_iUnion.mpr ⟨p, hself p⟩)
  obtain ⟨ε, hε, hεbound⟩ := exists_positive_lower_bound_on_finset centers ε₀
    (fun p _ => hε₀ p)
  let U : Set (X × X) := ⋃ p ∈ centers, patch p ×ˢ patch p
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
    apply hglobal f hf _ hclose
    intro x y hxy heq
    obtain ⟨p, hp⟩ := mem_iUnion.mp hxy
    obtain ⟨hpc, hx, hy⟩ := mem_iUnion.mp hp
    exact hlocal p f ((hprofiles p hpc).mono (hεbound p hpc)) hx hy heq

end R4Embedding
