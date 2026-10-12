import R4Embedding.ModelClassification
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! Two-dimensional smoothing reduced to one chart step.

A closed surface is covered by finitely many compact subsets of chart domains. Extending the
region where a homeomorphism is a local diffeomorphism over them one at a time gives a
homeomorphism that is a local diffeomorphism everywhere, hence a diffeomorphism. The chart
step itself (vertex, edge and face smoothing in one chart) is an explicit input here. -/

noncomputable section
namespace R4Embedding

open Manifold Set
open scoped ContDiff

universe u v

/-- One chart step of two-dimensional smoothing: smoothness near a compact set `K` is kept
while the smooth region is extended over a compact subset of a chart domain. -/
def SmoothingChartStep (M : Type u) [TopologicalSpace M] [ChartedSpace Plane M]
    (N : Type v) [TopologicalSpace N] [ChartedSpace Plane N] : Prop :=
  ∀ (h : M ≃ₜ N) (K : Set M), IsCompact K →
    (∃ V : Set M, IsOpen V ∧ K ⊆ V ∧ IsLocalDiffeomorphOn planeModel planeModel ∞ h V) →
    ∀ (x : M) (C : Set M), IsCompact C → C ⊆ (chartAt Plane x).source →
    ∃ g : M ≃ₜ N, ∃ V : Set M, IsOpen V ∧ K ∪ C ⊆ V ∧
      IsLocalDiffeomorphOn planeModel planeModel ∞ g V

variable {M : Type u} [TopologicalSpace M] [ChartedSpace Plane M] [CompactSpace M]
  {N : Type v} [TopologicalSpace N] [ChartedSpace Plane N]

theorem exists_isLocalDiffeomorph_of_chartStep (hstep : SmoothingChartStep M N)
    (h : M ≃ₜ N) : ∃ g : M ≃ₜ N, IsLocalDiffeomorph planeModel planeModel ∞ g := by
  classical
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace Plane M
  have hC : ∀ x : M, ∃ C : Set M, IsCompact C ∧ x ∈ interior C ∧
      C ⊆ (chartAt Plane x).source :=
    fun x => exists_compact_subset (chartAt Plane x).open_source (mem_chart_source Plane x)
  choose C hCc hCx hCs using hC
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => interior (C x))
    (fun _ => isOpen_interior) (fun x _ => mem_iUnion.2 ⟨x, hCx x⟩)
  have step : ∀ s : Finset M, ∃ g : M ≃ₜ N, ∃ V : Set M, IsOpen V ∧
      (⋃ x ∈ s, C x) ⊆ V ∧ IsLocalDiffeomorphOn planeModel planeModel ∞ g V := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨h, ∅, isOpen_empty, by simp, fun x => (notMem_empty _ x.2).elim⟩
    | @insert x s _ ih =>
      obtain ⟨g, V, hV, hsV, hg⟩ := ih
      have hK : IsCompact (⋃ y ∈ s, C y) := s.isCompact_biUnion fun y _ => hCc y
      obtain ⟨g', V', hV', hKV', hg'⟩ :=
        hstep g _ hK ⟨V, hV, hsV, hg⟩ x (C x) (hCc x) (hCs x)
      refine ⟨g', V', hV', ?_, hg'⟩
      rw [Finset.set_biUnion_insert]
      exact union_subset (subset_union_right.trans hKV') (subset_union_left.trans hKV')
  obtain ⟨g, V, -, hsV, hg⟩ := step t
  refine ⟨g, fun y => hg ⟨y, hsV ?_⟩⟩
  have hy := ht (mem_univ y)
  rw [mem_iUnion₂] at hy
  obtain ⟨x, hxt, hyx⟩ := hy
  exact mem_biUnion hxt (interior_subset hyx)

theorem nonempty_diffeomorph_of_chartStep [IsManifold planeModel ∞ M]
    [IsManifold planeModel ∞ N] (hstep : SmoothingChartStep M N) (h : M ≃ₜ N) :
    Nonempty (Diffeomorph planeModel planeModel M N ∞) := by
  obtain ⟨g, hg⟩ := exists_isLocalDiffeomorph_of_chartStep hstep h
  exact ⟨hg.diffeomorphOfBijective g.bijective⟩

/-- Smoothing onto the explicit models follows from the chart step. -/
theorem polynomialModelSmoothing_of_chartStep
    (hstep : ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace Plane M]
      [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] (g : ℕ),
      let _ := polynomialLevelChartedSpace g
      SmoothingChartStep M (PolynomialLevel g)) :
    PolynomialModelSmoothingStatement.{u} := by
  intro M _ _ _ _ _ g h
  let _ := polynomialLevelChartedSpace g
  have : IsManifold planeModel ∞ (PolynomialLevel g) := polynomialLevel_isManifold g
  exact nonempty_diffeomorph_of_chartStep (hstep M g) h

end R4Embedding
