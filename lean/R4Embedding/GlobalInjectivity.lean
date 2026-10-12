import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Linarith

/-! Local separation near the diagonal and uniform C⁰ control away from it
give global injectivity. Compactness supplies the positive separation margin. -/

namespace R4Embedding

open Set

variable {X Y : Type*} [MetricSpace Y]

/-- Two points stay separated under a sufficiently small perturbation. -/
theorem ne_of_dist_lt_half_separation
    {F f : X → Y} {x y : X} {δ ε : ℝ}
    (hsep : δ ≤ dist (F x) (F y)) (hsmall : 2 * ε < δ)
    (hx : dist (f x) (F x) < ε) (hy : dist (f y) (F y) < ε) :
    f x ≠ f y := by
  intro hxy
  have htriangle := dist_triangle (F x) (f x) (F y)
  have hfirst : dist (F x) (f x) < ε := by simpa only [dist_comm] using hx
  have hsecond : dist (f x) (F y) < ε := by rw [hxy]; exact hy
  linarith

/-- A relation containing the diagonal need not come from a metric on X. -/
theorem injective_of_local_and_separation
    {F f : X → Y} {U : Set (X × X)} {δ ε : ℝ}
    (hlocal : ∀ x y, (x, y) ∈ U → f x = f y → x = y)
    (hsep : ∀ x y, (x, y) ∉ U → δ ≤ dist (F x) (F y))
    (hsmall : 2 * ε < δ) (hclose : ∀ x, dist (f x) (F x) < ε) :
    Function.Injective f := by
  intro x y hxy
  by_cases hU : (x, y) ∈ U
  · exact hlocal x y hU hxy
  · exact False.elim (ne_of_dist_lt_half_separation (hsep x y hU)
      hsmall (hclose x) (hclose y) hxy)

variable [TopologicalSpace X]

/-- Compactness turns local separation near the diagonal into a uniform C⁰
tolerance for global embedding preservation. -/
theorem exists_embedding_tolerance [CompactSpace X]
    {F : X → Y} (hF : Continuous F) (hFinj : Function.Injective F)
    {U : Set (X × X)} (hU : IsOpen U) (hdiag : ∀ x, (x, x) ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ f : X → Y, Continuous f →
      (∀ x y, (x, y) ∈ U → f x = f y → x = y) →
      (∀ x, dist (f x) (F x) < ε) → Topology.IsClosedEmbedding f := by
  have hK : IsCompact Uᶜ := hU.isClosed_compl.isCompact
  have hd : Continuous (fun p : X × X => dist (F p.1) (F p.2)) :=
    (hF.comp continuous_fst).dist (hF.comp continuous_snd)
  by_cases hne : Uᶜ.Nonempty
  · obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne hd.continuousOn
    have hnep : F p.1 ≠ F p.2 := by
      intro heq
      have heq' := hFinj heq
      have hpdiag : p = (p.2, p.2) := Prod.ext heq' rfl
      exact hp (by rw [hpdiag]; exact hdiag p.2)
    have hpos : 0 < dist (F p.1) (F p.2) := dist_pos.mpr hnep
    refine ⟨dist (F p.1) (F p.2) / 3, by positivity, ?_⟩
    intro f hf hlocal hclose
    apply hf.isClosedEmbedding
    apply injective_of_local_and_separation hlocal
      (fun x y hxy => hmin hxy) _ hclose
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro f hf hlocal _
    apply hf.isClosedEmbedding
    intro x y hxy
    apply hlocal x y _ hxy
    by_contra hnot
    exact hne ⟨(x, y), hnot⟩

end R4Embedding
