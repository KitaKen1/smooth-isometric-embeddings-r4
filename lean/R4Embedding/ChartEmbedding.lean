import R4Embedding.ProjectedDerivative
import R4Embedding.GlobalInjectivity

/-! A chart certificate records exactly the analytic inputs required by the
fixed-projection argument. It does not assume that the perturbed map is injective.
No smooth-manifold existence theorem is asserted by this interface. -/

namespace R4Embedding

open Set

variable {X E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The coordinate and derivative data for one patch of the perturbed map. -/
structure ProjectedChartCertificate (patch : Set X) (f : X → V) where
  domain : Set E
  convex : Convex ℝ domain
  coordinates : X → E
  coordinates_mem : ∀ x ∈ patch, coordinates x ∈ domain
  coordinates_inj : Set.InjOn coordinates patch
  map : E → V
  map_eq : ∀ x ∈ patch, map (coordinates x) = f x
  projection : V →L[ℝ] E
  derivative : E → E →L[ℝ] V
  has_derivative : ∀ x ∈ domain, HasFDerivWithinAt map (derivative x) domain x
  error : ℝ
  error_lt_one : error < 1
  derivative_bound : ∀ x ∈ domain,
    ‖projection.comp (derivative x) - ContinuousLinearMap.id ℝ E‖ ≤ error

/-- A certificate proves local injectivity; injectivity is not a field of it. -/
theorem ProjectedChartCertificate.injOn {patch : Set X} {f : X → V}
    (C : ProjectedChartCertificate (E := E) patch f) : Set.InjOn f patch := by
  have h := injOn_of_projected_derivative_close_id C.projection C.convex
    C.has_derivative C.derivative_bound C.error_lt_one
  intro x hx y hy hxy
  apply C.coordinates_inj hx hy
  apply h (C.coordinates_mem x hx) (C.coordinates_mem y hy)
  rw [C.map_eq x hx, C.map_eq y hy]
  exact hxy

variable [TopologicalSpace X]

/-- Fixed open patches determine a tolerance before the perturbed map and its
oscillatory chart certificates are chosen. The index set need not be finite. -/
theorem exists_embedding_tolerance_of_projected_charts [CompactSpace X]
    {ι : Type*} (patch : ι → Set X)
    (hopen : ∀ i, IsOpen (patch i)) (hcover : ∀ x, ∃ i, x ∈ patch i)
    {F : X → V} (hF : Continuous F) (hFinj : Function.Injective F) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ f : X → V, Continuous f →
      (∀ i, Nonempty (ProjectedChartCertificate (E := E) (patch i) f)) →
      (∀ x, dist (f x) (F x) < ε) → Topology.IsClosedEmbedding f := by
  let U : Set (X × X) := ⋃ i, patch i ×ˢ patch i
  have hU : IsOpen U := isOpen_iUnion (fun i => (hopen i).prod (hopen i))
  have hdiag : ∀ x, (x, x) ∈ U := by
    intro x
    obtain ⟨i, hi⟩ := hcover x
    exact mem_iUnion.mpr ⟨i, hi, hi⟩
  obtain ⟨ε, hε, htol⟩ := exists_embedding_tolerance hF hFinj hU hdiag
  refine ⟨ε, hε, ?_⟩
  intro f hf hcert hclose
  apply htol f hf _ hclose
  intro x y hxy heq
  obtain ⟨i, hx, hy⟩ := mem_iUnion.mp hxy
  obtain ⟨C⟩ := hcert i
  exact C.injOn hx hy heq

end R4Embedding
