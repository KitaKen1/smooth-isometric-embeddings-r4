import R4Embedding.CoordinateRegions
import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-! A compact support transported through two genuine chart targets is
already closed. Its closure contains no extra points outside the chart.
Membership supplies an actual coordinate, not an inverse evaluated outside
the target of a partial homeomorphism. -/

noncomputable section
namespace R4Embedding

open Set

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [T2Space X]

theorem compact_chart_support_eq_image (c : OpenPartialHomeomorph X Y)
    (e : OpenPartialHomeomorph Y Z) {K : Set Z} (hK : IsCompact K)
    (hKe : K ⊆ e.target) (hKc : e.symm '' K ⊆ c.target) :
    closure (c.symm '' (e.symm '' K)) = c.symm '' (e.symm '' K) := by
  have heK : IsCompact (e.symm '' K) :=
    hK.image_of_continuousOn (e.symm.continuousOn.mono hKe)
  exact (heK.image_of_continuousOn (c.symm.continuousOn.mono hKc)).isClosed.closure_eq

theorem compact_chart_support_coordinate (c : OpenPartialHomeomorph X Y)
    (e : OpenPartialHomeomorph Y Z) {K : Set Z} (hK : IsCompact K)
    (hKe : K ⊆ e.target) (hKc : e.symm '' K ⊆ c.target)
    {p : X} (hp : p ∈ closure (c.symm '' (e.symm '' K))) :
    ∃ q ∈ K, p = (c.trans e).symm q ∧
      p ∈ (c.trans e).source ∧ (c.trans e) p = q := by
  rw [compact_chart_support_eq_image c e hK hKe hKc] at hp
  rcases hp with ⟨y, ⟨q, hq, rfl⟩, rfl⟩
  have ht : q ∈ (c.trans e).target := ⟨hKe hq, hKc ⟨q, hq, rfl⟩⟩
  exact ⟨q, hq, rfl, (c.trans e).map_target ht, (c.trans e).right_inv ht⟩

theorem compact_chart_support_subset_source (c : OpenPartialHomeomorph X Y)
    (e : OpenPartialHomeomorph Y Z) {K : Set Z} (hK : IsCompact K)
    (hKe : K ⊆ e.target) (hKc : e.symm '' K ⊆ c.target) :
    closure (c.symm '' (e.symm '' K)) ⊆ (c.trans e).source := by
  intro p hp
  obtain ⟨_, _, _, hs, _⟩ := compact_chart_support_coordinate c e hK hKe hKc hp
  exact hs

end R4Embedding
