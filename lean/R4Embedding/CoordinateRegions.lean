import R4Embedding.ProfileAtlas

/-! An outer cutoff which is locally constant on a closed support gives an
open coordinate region around every support point. Balls can be chosen in
this region even when the inner weight vanishes at the support boundary. -/

noncomputable section
namespace R4Embedding

open Set Filter
open scoped Topology

variable {X Y V : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def chartConstantRegion (e : OpenPartialHomeomorph X Y) (χ : X → V) (c : V) : Set Y :=
  e.target ∩ e.symm ⁻¹' interior {p | χ p = c}

theorem chartConstantRegion_isOpen (e : OpenPartialHomeomorph X Y) (χ : X → V) (c : V) :
    IsOpen (chartConstantRegion e χ c) :=
  e.symm.continuousOn.isOpen_inter_preimage e.open_target isOpen_interior

theorem mem_chartConstantRegion_of_locally_constant (e : OpenPartialHomeomorph X Y)
    (χ : X → V) (c : V) {p : X} (hp : p ∈ e.source)
    (hc : χ =ᶠ[𝓝 p] (fun _ => c)) : e p ∈ chartConstantRegion e χ c := by
  refine ⟨e.map_source hp, ?_⟩
  change e.symm (e p) ∈ interior {q | χ q = c}
  rw [e.left_inv hp]
  exact mem_interior_iff_mem_nhds.mpr hc

theorem locally_constant_of_mem_chartConstantRegion (e : OpenPartialHomeomorph X Y)
    (χ : X → V) (c : V) {q : Y} (hq : q ∈ chartConstantRegion e χ c) :
    χ =ᶠ[𝓝 (e.symm q)] (fun _ => c) :=
  mem_interior_iff_mem_nhds.mp hq.2

end R4Embedding
