import R4Initial.SmoothingReduction
import DifferentialGeometry.Topology.Manifold.SurfaceSimplicialSkeleton
import DifferentialGeometry.Topology.Manifold.SurfaceTriangleReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCellCover
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexComplex
import DifferentialGeometry.Topology.PiecewiseLinear.Cone
import DifferentialGeometry.Topology.PiecewiseLinear.Combinatorial
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Chart
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Locus

/-! The chart step of two-dimensional smoothing, relative to a closed set.

A homeomorphism between smooth surfaces that is already a local diffeomorphism near a closed
set `Z` is changed into one that is a local diffeomorphism at every point of `Z` and of a
simplex in one chart. The simplex is subdivided so finely that each vertex star is either
inside the smooth region or away from `Z`, and each face maps into one chart of the target.
Vertices and edges away from `Z` are smoothed with supports away from `Z` and from the frozen
vertices and edges (qinz1yang's point and segment smoothing); then every triangle is replaced
inside a smooth Jordan curve near its boundary (qinz1yang's disk replacement, which keeps all
smooth points). Covering a compact subset of a chart by finitely many simplices proves
`SmoothingChartStep`, hence the smoothing statement for the explicit models.

This file imports the smoothing tools but not Lean Pool: qinz1yang's library vendors part of the
same classification project under the same declaration names, so the two cannot be loaded into
one environment unchanged (see `VENDOR-CLASH.md`). -/

noncomputable section
namespace R4Embedding

open Set Filter Topology
open scoped ContDiff Manifold
open DifferentialGeometry.Topology.PiecewiseLinear
open DifferentialGeometry.Topology.PlanarJordan

universe u

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [T2Space M] [T2Space N] [ChartedSpace Plane M] [ChartedSpace Plane N]
  [IsManifold planeModel ∞ M] [IsManifold planeModel ∞ N]

/-- Vertices and edges of a planar complex in one chart are made smooth by changes away from a
closed set `Z`, provided every vertex star is either disjoint from `Z` or already smooth. -/
theorem exists_smooth_skeleton_away (h : M ≃ₜ N)
    (a : PartialDiffeomorph planeModel planeModel M Plane ∞)
    (K : Geometry.SimplicialComplex ℝ Plane) [Finite K.faces] (hKa : K.space ⊆ a.target)
    (b : K.faces → PartialDiffeomorph planeModel planeModel N Plane ∞)
    (hb : ∀ s : K.faces, h '' (a.symm '' convexHull ℝ (s.val : Set Plane)) ⊆ (b s).source)
    {Z : Set M} (hZ : IsClosed Z)
    (hstar : ∀ v ∈ K.vertices, Disjoint (a.symm '' closedStar K v) Z ∨
      IsLocalDiffeomorphOn planeModel planeModel ∞ h (a.symm '' closedStar K v)) :
    ∃ L : Set M, IsCompact L ∧ Disjoint L Z ∧ ∃ g : M ≃ₜ N, EqOn g h Lᶜ ∧
      (∀ s : K.faces, g '' (a.symm '' convexHull ℝ (s.val : Set Plane)) ⊆ (b s).source) ∧
      ∀ s ∈ K.faces, s.card ≤ 2 → IsLocalDiffeomorphOn planeModel planeModel ∞ g
        (a.symm '' convexHull ℝ (s : Set Plane)) := by
  classical
  let act : Plane → Prop := fun v => Disjoint (a.symm '' closedStar K v) Z
  let C (s : K.faces) := a.symm '' convexHull ℝ (s.val : Set Plane)
  have hfa {s : Finset Plane} (hs : s ∈ K.faces) : convexHull ℝ (s : Set Plane) ⊆ a.target :=
    (K.convexHull_subset_space hs).trans hKa
  have hC (s : K.faces) : IsCompact (C s) :=
    (s.val.finite_toSet.isCompact_convexHull ℝ).image_of_continuousOn
      (a.symm.toOpenPartialHomeomorph.continuousOn.mono (hfa s.property))
  have hdisimage {s t : Set Plane} (hs : s ⊆ a.target) (ht : t ⊆ a.target)
      (hd : Disjoint s t) : Disjoint (a.symm '' s) (a.symm '' t) := by
    apply disjoint_left.mpr
    rintro x ⟨v, hv, hvx⟩ ⟨w, hw, hwx⟩
    have hvw := a.symm.toOpenPartialHomeomorph.injOn (hs hv) (ht hw) (hvx.trans hwx.symm)
    exact disjoint_left.mp hd hv (hvw.symm ▸ hw)
  have hvface {v : Plane} {s : Finset Plane} (hs : s ∈ K.faces) (hv : v ∈ s) :
      {v} ∈ K.faces :=
    K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hhull_star {v : Plane} {s : Finset Plane} (hs : s ∈ K.faces) (hv : v ∈ s) :
      convexHull ℝ (s : Set Plane) ⊆ closedStar K v := fun x hx =>
    mem_biUnion (x := s) ⟨hs, subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)⟩ hx
  -- Frozen vertices and edges: all their vertices have stars meeting `Z`.
  let Fz : Set (Finset Plane) := {s | s ∈ K.faces ∧ s.card ≤ 2 ∧ ∀ v ∈ s, ¬ act v}
  have hFzfin : Fz.Finite := (Set.toFinite K.faces).subset fun s hs => hs.1
  let Fr : Set M := ⋃ s ∈ Fz, a.symm '' convexHull ℝ (s : Set Plane)
  have hFr : IsClosed Fr := hFzfin.isClosed_biUnion fun s hs =>
    ((s.finite_toSet.isCompact_convexHull ℝ).image_of_continuousOn
      (a.symm.toOpenPartialHomeomorph.continuousOn.mono (hfa hs.1))).isClosed
  let U : Set M := (Z ∪ Fr)ᶜ
  have hU : IsOpen U := (hZ.union hFr).isOpen_compl
  have hfrozen_smooth {s : Finset Plane} (hs : s ∈ Fz) :
      IsLocalDiffeomorphOn planeModel planeModel ∞ h
        (a.symm '' convexHull ℝ (s : Set Plane)) := by
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs.1
    rcases hstar v (hvface hs.1 hv) with hact | hsm
    · exact absurd hact (hs.2.2 v hv)
    · exact fun x => hsm ⟨x, image_mono (hhull_star hs.1 hv) x.property⟩
  have hactU {v : Plane} (hv : v ∈ K.vertices) (hact : act v) : a.symm v ∈ U := by
    have hvstar : a.symm v ∈ a.symm '' closedStar K v :=
      mem_image_of_mem _ (mem_closedStar_self K hv)
    rintro (hvZ | hvFr)
    · exact disjoint_left.mp hact hvstar hvZ
    · obtain ⟨s, hs, w, hw, hwv⟩ := mem_iUnion₂.mp hvFr
      have hwv' : w = v := a.symm.toOpenPartialHomeomorph.injOn (hfa hs.1 hw)
        (hKa (K.vertices_subset_space hv)) hwv
      rw [hwv'] at hw
      exact hs.2.2 v (mem_of_mem_convexHull_of_singleton_mem K hv hs.1 hw) hact
  -- Step 1: the vertices whose stars avoid `Z`.
  have hVfin : K.vertices.Finite := by
    rw [K.vertices_eq]
    exact (Set.toFinite K.faces).biUnion fun s _ => s.finite_toSet
  let P := a.symm '' K.vertices
  have hPfin : P.Finite := hVfin.image _
  let Tv : Set M := a.symm '' {v | v ∈ K.vertices ∧ act v}
  have hTvfin : Tv.Finite := (hVfin.subset fun v hv => hv.1).image _
  let T := hTvfin.toFinset
  have hTU : (T : Set M) ⊆ U := by
    simp only [T, Set.Finite.coe_toFinset]
    rintro _ ⟨v, ⟨hv, hact⟩, rfl⟩
    exact hactU hv hact
  obtain ⟨L₀, hL₀, hL₀U, g₀, hg₀out, -, hg₀T, hg₀map⟩ :=
    h.exists_smooth_on_finset_preserving_mapsTo C (fun s => (b s).source)
      (fun s => (hC s).isClosed) (fun s => (b s).open_source)
      (fun s => mapsTo_iff_image_subset.mpr (hb s)) T hU hTU
  have hg₀ext {x : M} (hx : x ∉ L₀)
      (hh : IsLocalDiffeomorphAt planeModel planeModel ∞ h x) :
      IsLocalDiffeomorphAt planeModel planeModel ∞ g₀ x := by
    apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq (g := h) _ hh
    filter_upwards [hL₀.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact hg₀out hy
  have hg₀P : IsLocalDiffeomorphOn planeModel planeModel ∞ g₀ P := by
    rintro ⟨_, v, hv, rfl⟩
    by_cases hact : act v
    · exact hg₀T ⟨a.symm v, by
        simp only [T, Set.Finite.coe_toFinset]
        exact ⟨v, ⟨hv, hact⟩, rfl⟩⟩
    · have hFz : ({v} : Finset Plane) ∈ Fz := ⟨hv, by simp, fun w hw => by
        rw [Finset.mem_singleton] at hw
        rw [hw]
        exact hact⟩
      have hvFr : a.symm v ∈ Fr := mem_iUnion₂.mpr ⟨{v}, hFz, v, by simp, rfl⟩
      exact hg₀ext (fun hxL => hL₀U hxL (Or.inr hvFr))
        (hfrozen_smooth hFz ⟨a.symm v, v, by simp, rfl⟩)
  -- Step 2: the edges with a vertex whose star avoids `Z`.
  let E := {s : K.faces // s.val.card = 2 ∧ ∃ v ∈ s.val, act v}
  have hpairs (i : E) : ∃ p q : Plane, p ≠ q ∧ i.val.val = {p, q} :=
    Finset.card_eq_two.mp i.property.1
  choose p q hpq hpqs using hpairs
  choose D hD using fun i => exists_diffeomorph_lineMap (hpq i)
  let A (i : E) := (D i).toPartialDiffeomorph.trans a.symm
  let σ : ℝ → Plane := fun t => Schoenflies.Plane.mk t 0
  have hA (i : E) (t : ℝ) : A i (σ t) = a.symm (AffineMap.lineMap (p i) (q i) t) := by
    change a.symm (D i (Schoenflies.Plane.mk t 0)) = _
    rw [hD]
  have hseg (i : E) : convexHull ℝ (i.val.val : Set Plane) =
      AffineMap.lineMap (p i) (q i) '' Icc (0 : ℝ) 1 := by
    rw [hpqs i]
    simp only [Finset.coe_pair, convexHull_pair, segment_eq_image_lineMap]
  have hopen (i : E) : openSimplex i.val.val =
      AffineMap.lineMap (p i) (q i) '' Ioo (0 : ℝ) 1 := by
    rw [hpqs i]
    exact (openSimplex_pair_eq_openSegment (hpq i)).trans
      (openSegment_eq_image_lineMap ℝ (p i) (q i))
  have hAS (i : E) : A i '' (σ '' Icc (0 : ℝ) 1) = C i.val := by
    rw [image_image, show C i.val = a.symm '' convexHull ℝ (i.val.val : Set Plane) from rfl,
      hseg, image_image]
    exact image_congr fun t _ => hA i t
  have hAO (i : E) : A i '' (σ '' Ioo (0 : ℝ) 1) = a.symm '' openSimplex i.val.val := by
    rw [image_image, hopen, image_image]
    exact image_congr fun t _ => hA i t
  have hhas (i : E) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : σ t ∈ (A i).source := by
    refine ⟨trivial, ?_⟩
    change D i (σ t) ∈ a.target
    rw [hD]
    apply hKa (K.convexHull_subset_space i.val.property _)
    rw [hseg]
    exact mem_image_of_mem _ ht
  have hmem (i : E) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : A i (σ t) ∈ C i.val :=
    hAS i ▸ mem_image_of_mem (A i) (mem_image_of_mem σ ht)
  have hinc (i : E) (s : K.faces) : A i '' (σ '' Icc (0 : ℝ) 1) ⊆ C s ∨
      Disjoint (A i '' (σ '' Ioo (0 : ℝ) 1)) (C s) := by
    rw [hAS, hAO]
    rcases convexHull_subset_or_disjoint_openSimplex K i.val.property s.property with hc | hd
    · exact Or.inl (image_mono hc)
    · exact Or.inr (hdisimage ((openSimplex_subset_convexHull _).trans (hfa i.val.property))
        (hfa s.property) hd)
  have hdis : Pairwise fun i j : E =>
      Disjoint (A i '' (σ '' Ioo (0 : ℝ) 1)) (A j '' (σ '' Icc (0 : ℝ) 1)) := by
    intro i j hij
    rw [hAO, hAS]
    exact hdisimage ((openSimplex_subset_convexHull _).trans (hfa i.val.property))
      (hfa j.val.property)
      (disjoint_openSimplex_convexHull_of_card_eq K i.val.property j.val.property
        (i.property.1.trans j.property.1.symm)
        (fun heq => hij (Subtype.ext (Subtype.ext heq))))
  have hends (i : E) : A i (σ 0) ∈ P ∧ A i (σ 1) ∈ P := by
    have hp : p i ∈ K.vertices := K.down_closed i.val.property
      (Finset.singleton_subset_iff.mpr (by rw [hpqs]; simp)) (by simp)
    have hq : q i ∈ K.vertices := K.down_closed i.val.property
      (Finset.singleton_subset_iff.mpr (by rw [hpqs]; simp)) (by simp)
    simpa only [hA, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using
      And.intro (mem_image_of_mem a.symm hp) (mem_image_of_mem a.symm hq)
  have hAU (i : E) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : A i (σ t) ∈ U \ P := by
    have hx : A i (σ t) ∈ a.symm '' openSimplex i.val.val :=
      hAO i ▸ mem_image_of_mem (A i) (mem_image_of_mem σ ht)
    have hface := i.val.property
    have hopen_sub : openSimplex i.val.val ⊆ a.target :=
      (openSimplex_subset_convexHull _).trans (hfa hface)
    obtain ⟨r, hr, hract⟩ := i.property.2
    refine ⟨?_, fun hxp => disjoint_left.mp (hdisimage hopen_sub
      (K.vertices_subset_space.trans hKa)
      (disjoint_openSimplex_vertices_of_one_lt_card K hface (by rw [i.property.1]; norm_num)))
      hx hxp⟩
    rintro (hxZ | hxFr)
    · exact disjoint_left.mp hract
        (image_mono ((openSimplex_subset_convexHull _).trans (hhull_star hface hr)) hx) hxZ
    · obtain ⟨s, hs, w, hw, hwx⟩ := mem_iUnion₂.mp hxFr
      obtain ⟨u, hu, hux⟩ := hx
      have huw : u = w := a.symm.toOpenPartialHomeomorph.injOn (hopen_sub hu) (hfa hs.1 hw)
        (hux.trans hwx.symm)
      rw [huw] at hu
      exact hs.2.2 r (face_subset_of_mem_openSimplex_of_mem_convexHull K hface hs.1 hu hw hr)
        hract
  obtain ⟨L₁, hL₁, hL₁U, g, hgout, hgmap, hgseg⟩ :=
    g₀.exists_smooth_finite_segments_preserving_mapsTo A (fun i => b i.val) hhas
      (fun i t ht => hg₀map i.val (hmem i t ht)) C (fun s => (b s).source)
      (fun s => (hC s).isClosed) (fun s => (b s).open_source) hg₀map hinc hdis
      hPfin.isClosed hU hg₀P (fun i => (hends i).1) (fun i => (hends i).2) hAU
  have hgext {x : M} (hx : x ∉ L₁)
      (hh : IsLocalDiffeomorphAt planeModel planeModel ∞ g₀ x) :
      IsLocalDiffeomorphAt planeModel planeModel ∞ g x := by
    apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq (g := g₀) _ hh
    filter_upwards [hL₁.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact hgout hy
  have hgP : IsLocalDiffeomorphOn planeModel planeModel ∞ g P :=
    fun x => hgext (fun hxL => (hL₁U hxL).2 x.property) (hg₀P x)
  refine ⟨L₀ ∪ L₁, hL₀.union hL₁, ?_, g, ?_, fun s => mapsTo_iff_image_subset.mp (hgmap s), ?_⟩
  · refine disjoint_left.mpr fun x hxL hxZ => ?_
    rcases hxL with hx | hx
    · exact hL₀U hx (Or.inl hxZ)
    · exact (hL₁U hx).1 (Or.inl hxZ)
  · intro x hx
    exact (hgout (fun hxL => hx (Or.inr hxL))).trans
      (hg₀out (fun hxL => hx (Or.inl hxL)))
  · intro s hs hcard x
    obtain ⟨v, hv, hvx⟩ := x.property
    have hpos : 0 < s.card := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
    by_cases hs1 : s.card = 1
    · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp hs1
      have hvw : v = w := by simpa using hv
      subst v
      exact hgP ⟨x, hvx ▸ mem_image_of_mem a.symm hs⟩
    · have hs2 : s.card = 2 := by omega
      by_cases hsact : ∃ r ∈ s, act r
      · let i : E := ⟨⟨s, hs⟩, hs2, hsact⟩
        have hxS : (x : M) ∈ A i '' (σ '' Icc (0 : ℝ) 1) := (hAS i).symm ▸ x.property
        obtain ⟨_, ⟨t, ht, rfl⟩, htx⟩ := hxS
        exact htx ▸ hgseg i t ht
      · have hFz : s ∈ Fz := ⟨hs, hcard, fun r hr hract => hsact ⟨r, hr, hract⟩⟩
        have hxFr : (x : M) ∈ Fr := mem_iUnion₂.mpr ⟨s, hFz, x.property⟩
        exact hgext (fun hxL => (hL₁U hxL).1 (Or.inr hxFr))
          (hg₀ext (fun hxL => hL₀U hxL (Or.inr hxFr)) (hfrozen_smooth hFz x))

/-- Triangles in one chart whose boundaries are already smooth are made smooth, keeping every
point where the homeomorphism was already a local diffeomorphism. -/
theorem exists_smooth_triangles_keeping {ι : Type*} [Finite ι] (h : M ≃ₜ N)
    (a : PartialDiffeomorph planeModel planeModel M Plane ∞)
    (b : ι → PartialDiffeomorph planeModel planeModel N Plane ∞)
    (t : ι → AffineBasis (Fin 3) ℝ Plane)
    (hta : ∀ i, convexHull ℝ (range (t i)) ⊆ a.target)
    (htb : ∀ i, h '' (a.symm '' convexHull ℝ (range (t i))) ⊆ (b i).source)
    (hdisjoint : Pairwise fun i j => Disjoint
      (interior (convexHull ℝ (range (t i)))) (interior (convexHull ℝ (range (t j)))))
    (hboundary : ∀ i, ∀ x ∈ a.symm '' frontier (convexHull ℝ (range (t i))),
      IsLocalDiffeomorphAt planeModel planeModel ∞ h x) :
    ∃ g : M ≃ₜ N, (∀ x, IsLocalDiffeomorphAt planeModel planeModel ∞ h x →
        IsLocalDiffeomorphAt planeModel planeModel ∞ g x) ∧
      ∀ i, ∀ x ∈ a.symm '' convexHull ℝ (range (t i)),
        IsLocalDiffeomorphAt planeModel planeModel ∞ g x := by
  classical
  let U : Set M := {x | IsLocalDiffeomorphAt planeModel planeModel ∞ h x}
  have hU : IsOpen U := isOpen_setOf_isLocalDiffeomorphAt _ _ _ _
  have hlocal : IsLocalDiffeomorphOn planeModel planeModel ∞ h U := fun x => x.property
  let C (i : ι) := convexHull ℝ (range (t i))
  have hC (i : ι) : IsCompact (C i) := (finite_range (t i)).isCompact_convexHull ℝ
  let W := a.target ∩ a.symm ⁻¹' U
  have hW : IsOpen W := a.toOpenPartialHomeomorph.isOpen_inter_preimage_symm hU
  have hCW (i : ι) : frontier (C i) ⊆ W := fun x hx =>
    ⟨hta i ((hC i).isClosed.frontier_subset hx), hboundary i _ ⟨x, hx, rfl⟩⟩
  have hcores (i : ι) :=
    DifferentialGeometry.Topology.Planar.exists_smooth_jordan_core_triangle (t i) hW (hCW i)
  choose γ hγ hQsub hrest using hcores
  let Q (i : ι) := closure (Schoenflies.inside (range (γ i)))
  let K (i : ι) := a.symm '' Q i
  have hQt (i : ι) : Q i ⊆ a.target := (hQsub i).trans (interior_subset.trans (hta i))
  have hQ (i : ι) : IsCompact (Q i) :=
    (hC i).of_isClosed_subset isClosed_closure ((hQsub i).trans interior_subset)
  have hK (i : ι) : IsCompact (K i) := (hQ i).image_of_continuousOn
    (a.symm.toOpenPartialHomeomorph.continuousOn.mono (hQt i))
  have hKa (i : ι) : K i ⊆ a.source := by
    rintro _ ⟨x, hx, rfl⟩
    exact a.map_target (hQt i hx)
  have hKC (i : ι) : K i ⊆ a.symm '' C i :=
    image_mono ((hQsub i).trans interior_subset)
  have hKb (i : ι) : h '' K i ⊆ (b i).source := (image_mono (hKC i)).trans (htb i)
  have hcoord (i : ι) : a '' K i = Q i := by
    ext z
    constructor
    · rintro ⟨x, ⟨v, hv, rfl⟩, rfl⟩
      -- the coercions of `a` and `a.symm` in the goal go through `toPartialEquiv`, so close the
      -- membership by definitional unfolding instead of rewriting
      exact (congrArg (· ∈ Q i) (a.right_inv (hQt i hv))).mpr hv
    · intro hz
      exact ⟨a.symm z, ⟨z, hz, rfl⟩, a.right_inv (hQt i hz)⟩
  have hdis : Pairwise fun i j => Disjoint (K i) (K j) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro x ⟨v, hv, hvx⟩ ⟨w, hw, hwx⟩
    have hvw : v = w := a.symm.toOpenPartialHomeomorph.injOn
      (hQt i hv) (hQt j hw) (hvx.trans hwx.symm)
    exact disjoint_left.mp (hdisjoint hij) (hQsub i hv) (hvw.symm ▸ hQsub j hw)
  have hJ (i : ι) : Schoenflies.IsJordanCurve (range (γ i)) :=
    isJordanCurve_range_of_isEmbedding_addCircle one_ne_zero (hγ i).isEmbedding
  have hfront (i : ι) : frontier (K i) = a.symm '' range (γ i) := by
    change frontier (a.symm.toOpenPartialHomeomorph '' Q i) =
      a.symm.toOpenPartialHomeomorph '' range (γ i)
    rw [← a.symm.toOpenPartialHomeomorph.image_frontier_of_isCompact (hQ i) (hQt i)]
    rw [show frontier (Q i) = range (γ i) from frontier_closure_inside (hJ i)]
  have hγQ (i : ι) : range (γ i) ⊆ Q i := by
    rw [← frontier_closure_inside (hJ i)]
    exact isClosed_closure.frontier_subset
  have hKU (i : ι) : frontier (K i) ⊆ U := by
    rw [hfront i]
    rintro _ ⟨v, hv, rfl⟩
    have hvC : v ∈ C i := interior_subset (hQsub i (hγQ i hv))
    exact (hrest i ⟨hvC, fun hvIn => Schoenflies.inside_subset_compl hvIn hv⟩).2
  obtain ⟨g, -, -, hgpres, hgK⟩ := exists_homeomorph_smoothing_finite_disjoint_disks h
    (fun _ => a) b K hK hdis hKa hKb γ hγ hcoord (fun _ => U) (fun _ => hU) hKU
    (fun _ => hlocal)
  refine ⟨g, hgpres, fun i x hx => ?_⟩
  obtain ⟨v, hvC, rfl⟩ := hx
  by_cases hvQ : v ∈ Q i
  · exact hgK i ⟨a.symm v, v, hvQ, rfl⟩
  · exact hgpres _ (hrest i ⟨hvC, fun hvIn => hvQ (subset_closure hvIn)⟩).2

/-- Smoothing over one simplex in a chart, keeping a closed set where the homeomorphism is
already a local diffeomorphism nearby. -/
theorem exists_smooth_on_simplex_keeping (h : M ≃ₜ N)
    (a : PartialDiffeomorph planeModel planeModel M Plane ∞)
    {T : Finset Plane} (hT : AffineIndependent ℝ ((↑) : T → Plane)) (hTne : T.Nonempty)
    (hTa : convexHull ℝ (T : Set Plane) ⊆ a.target)
    {Z V : Set M} (hZ : IsClosed Z) (hV : IsOpen V) (hZV : Z ⊆ V)
    (hh : IsLocalDiffeomorphOn planeModel planeModel ∞ h V) :
    ∃ g : M ≃ₜ N, ∀ x ∈ Z ∪ a.symm '' convexHull ℝ (T : Set Plane),
      IsLocalDiffeomorphAt planeModel planeModel ∞ g x := by
  classical
  -- charts of the target and the open cover of the simplex
  let c (y : N) : PartialDiffeomorph planeModel planeModel N Plane ∞ :=
    DifferentialGeometry.PartialDiffeomorph.extChartAt planeModel ∞ y
  have hcy (y : N) : y ∈ (c y).source := mem_extChartAt_source (I := planeModel) y
  let sel : N ⊕ N → N := Sum.elim id id
  let Ucov : N ⊕ N → Set Plane := fun i =>
    a.target ∩ a.symm ⁻¹' (Sum.elim (fun _ => V) (fun _ => Zᶜ) i ∩ h ⁻¹' (c (sel i)).source)
  have hUcov (i : N ⊕ N) : IsOpen (Ucov i) := by
    refine a.symm.toOpenPartialHomeomorph.continuousOn.isOpen_inter_preimage a.open_target
      (IsOpen.inter ?_ ((c (sel i)).open_source.preimage h.continuous))
    rcases i with y | y
    · exact hV
    · exact hZ.isOpen_compl
  have hsplit (i : N ⊕ N) :
      (∀ x ∈ Ucov i, a.symm x ∈ V) ∨ (∀ x ∈ Ucov i, a.symm x ∉ Z) := by
    rcases i with y | y
    · exact Or.inl fun x hx => hx.2.1
    · exact Or.inr fun x hx => hx.2.1
  have hcover : ∀ x ∈ convexHull ℝ (T : Set Plane), ∃ i, x ∈ Ucov i := by
    intro x hx
    by_cases hxZ : a.symm x ∈ Z
    · exact ⟨Sum.inl (h (a.symm x)), hTa hx, hZV hxZ, hcy _⟩
    · exact ⟨Sum.inr (h (a.symm x)), hTa hx, hxZ, hcy _⟩
  -- a fine subdivision of the simplex
  have hK₁ : (simplexComplex T hT).space = convexHull ℝ (T : Set Plane) :=
    simplexComplex_space T hT hTne
  have := (simplexComplex_faces_finite T hT).to_subtype
  obtain ⟨R, hRK, hRfin, -, -, hRcov⟩ :=
    exists_isSubdivision_derivedCells_subset_cover (simplexComplex T hT)
      ((isHPolytope_convexHull_of_affineIndependent T hT).isPolyhedron) hK₁.symm.subset
      (fun i : Empty => i.elim) (fun i => i.elim) (fun i => i.elim) Ucov hUcov hcover
  have := hRfin.to_subtype
  have hRspace : R.space = convexHull ℝ (T : Set Plane) := hRK.space_eq.trans hK₁
  have hRa : R.space ⊆ a.target := hRspace.subset.trans hTa
  have hstar_cov (s : R.faces) : ∃ i, (⋃ v ∈ s.val, closedStar R v) ⊆ Ucov i :=
    (hRcov s.val ⟨s.property, (R.convexHull_subset_space s.property).trans hRspace.subset⟩).imp
      fun _ hi => hi.1
  choose idx hidx using hstar_cov
  let b (s : R.faces) := c (sel (idx s))
  have hface_star {s : Finset Plane} (hs : s ∈ R.faces) {v : Plane} (hv : v ∈ s) :
      convexHull ℝ (s : Set Plane) ⊆ ⋃ w ∈ s, closedStar R w := fun x hx =>
    mem_iUnion₂.mpr ⟨v, hv, mem_biUnion (x := s)
      ⟨hs, subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)⟩ hx⟩
  have hb : ∀ s : R.faces, h '' (a.symm '' convexHull ℝ (s.val : Set Plane)) ⊆ (b s).source := by
    rintro s _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨v, hv⟩ := R.nonempty_of_mem_faces s.property
    exact (hidx s (hface_star s.property hv hx)).2.2
  have hstarR : ∀ v ∈ R.vertices, Disjoint (a.symm '' closedStar R v) Z ∨
      IsLocalDiffeomorphOn planeModel planeModel ∞ h (a.symm '' closedStar R v) := by
    intro v hv
    have hsub : ∀ x ∈ closedStar R v, x ∈ Ucov (idx ⟨{v}, hv⟩) := fun x hx =>
      hidx ⟨{v}, hv⟩ (mem_iUnion₂.mpr ⟨v, Finset.mem_singleton_self v, hx⟩)
    rcases hsplit (idx ⟨{v}, hv⟩) with hVi | hZi
    · right
      rintro ⟨_, x, hx, rfl⟩
      exact hh ⟨_, hVi x (hsub x hx)⟩
    · left
      refine disjoint_left.mpr ?_
      rintro _ ⟨x, hx, rfl⟩ hxZ
      exact hZi x (hsub x hx) hxZ
  -- vertices and edges, then triangles
  obtain ⟨L, hL, hLZ, g₁, hg₁out, hg₁map, hg₁skel⟩ :=
    exists_smooth_skeleton_away h a R hRa b hb hZ hstarR
  let F := {s : R.faces // s.val.card = 3}
  have hcard (i : F) : i.val.val.card = Module.finrank ℝ Plane + 1 := by
    rw [i.property, finrank_euclideanSpace_fin]
  have hbases (i : F) :
      ∃ t : AffineBasis (Fin 3) ℝ Plane, range t = (i.val.val : Set Plane) := by
    have htop : affineSpan ℝ (range ((↑) : i.val.val → Plane)) = ⊤ :=
      (R.indep i.val.property).affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
        (by simpa only [Fintype.card_coe] using hcard i)
    let t : AffineBasis i.val.val ℝ Plane := ⟨Subtype.val, R.indep i.val.property, htop⟩
    let e : i.val.val ≃ Fin 3 := Fintype.equivFinOfCardEq (by simpa using i.property)
    refine ⟨t.reindex e, ?_⟩
    change range (fun j => ((e.symm j : i.val.val) : Plane)) = (i.val.val : Set Plane)
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact (e.symm j).property
    · intro hx
      exact ⟨e ⟨x, hx⟩, congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)⟩
  choose t ht using hbases
  have hta (i : F) : convexHull ℝ (range (t i)) ⊆ a.target := by
    rw [ht]
    exact (R.convexHull_subset_space i.val.property).trans hRa
  have htb (i : F) : g₁ '' (a.symm '' convexHull ℝ (range (t i))) ⊆ (b i.val).source := by
    rw [ht]
    exact hg₁map i.val
  have hdis : Pairwise fun i j : F => Disjoint
      (interior (convexHull ℝ (range (t i)))) (interior (convexHull ℝ (range (t j)))) := by
    intro i j hij
    rw [ht, ht, interior_convexHull_eq_openSimplex (R.indep i.val.property) (hcard i),
      interior_convexHull_eq_openSimplex (R.indep j.val.property) (hcard j)]
    exact disjoint_left.mpr fun x hxi hxj => hij (Subtype.ext (Subtype.ext
      (face_eq_of_mem_openSimplex R i.val.property j.val.property hxi hxj)))
  have hbd (i : F) : ∀ x ∈ a.symm '' frontier (convexHull ℝ (range (t i))),
      IsLocalDiffeomorphAt planeModel planeModel ∞ g₁ x := by
    rw [ht, frontier_convexHull_eq_simplexBoundary (R.indep i.val.property) (hcard i)]
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨s, hs, hvs⟩ :=
      (simplexBoundary i.val.val (R.indep i.val.property)).mem_space_iff.mp hv
    have hsR : s ∈ R.faces := R.down_closed i.val.property hs.1 hs.2.1
    have hlt : s.card < i.val.val.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hs.1, hs.2.2⟩)
    have hs2 : s.card ≤ 2 := by rw [i.property] at hlt; omega
    exact hg₁skel s hsR hs2 ⟨_, v, hvs, rfl⟩
  obtain ⟨g, hgpres, hgtri⟩ :=
    exists_smooth_triangles_keeping g₁ a (fun i : F => b i.val) t hta htb hdis hbd
  refine ⟨g, fun x hx => ?_⟩
  rcases hx with hxZ | ⟨v, hv, rfl⟩
  · apply hgpres
    apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq (g := h) _ (hh ⟨x, hZV hxZ⟩)
    filter_upwards [hL.isClosed.isOpen_compl.mem_nhds (disjoint_right.mp hLZ hxZ)] with y hy
    exact hg₁out hy
  · obtain ⟨s, hs, hvs⟩ := exists_face_mem_openSimplex R (hRspace.symm.subset hv)
    have hle : s.card ≤ 3 := by
      simpa only [finrank_euclideanSpace_fin] using card_le_finrank_succ_of_mem_faces R hs
    by_cases hs3 : s.card = 3
    · let i : F := ⟨⟨s, hs⟩, hs3⟩
      refine hgtri i _ ⟨v, ?_, rfl⟩
      rw [ht]
      exact openSimplex_subset_convexHull _ hvs
    · exact hgpres _ (hg₁skel s hs (by omega) ⟨_, v, openSimplex_subset_convexHull _ hvs, rfl⟩)

/-- The chart step of smoothing holds between any two smooth Hausdorff surfaces. -/
theorem smoothingChartStep_holds : SmoothingChartStep M N := by
  intro h K hK hKs x C hC hCx
  obtain ⟨V, hV, hKV, hhV⟩ := hKs
  classical
  let a : PartialDiffeomorph planeModel planeModel M Plane ∞ :=
    DifferentialGeometry.PartialDiffeomorph.extChartAt planeModel ∞ x
  have hsrc : a.source = (chartAt Plane x).source := extChartAt_source (I := planeModel) x
  have hCa : C ⊆ a.source := hsrc ▸ hCx
  have hDc : IsCompact (a '' C) :=
    hC.image_of_continuousOn (a.toOpenPartialHomeomorph.continuousOn.mono hCa)
  have hDa : a '' C ⊆ a.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact a.map_source (hCa hy)
  have hsimplex : ∀ p ∈ a.target, ∃ T : Finset Plane, AffineIndependent ℝ ((↑) : T → Plane) ∧
      T.Nonempty ∧ convexHull ℝ (T : Set Plane) ⊆ a.target ∧
      convexHull ℝ (T : Set Plane) ∈ 𝓝 p := by
    intro p hp
    obtain ⟨T, hT, hTc, -, hTa, hTn⟩ := exists_affineIndependent_openSimplex_subset (n := 1)
      (by norm_num [finrank_euclideanSpace_fin]) p (a.open_target.mem_nhds hp)
    exact ⟨T, hT, Finset.card_pos.mp (by omega), hTa, hTn⟩
  choose! S hS using hsimplex
  let piece (p : Plane) : Set M := a.symm '' convexHull ℝ (S p : Set Plane)
  have hpiece (p : Plane) (hp : p ∈ a.target) : IsCompact (piece p) :=
    ((S p).finite_toSet.isCompact_convexHull ℝ).image_of_continuousOn
      (a.symm.toOpenPartialHomeomorph.continuousOn.mono (hS p hp).2.2.1)
  have step : ∀ s : Finset Plane, (∀ p ∈ s, p ∈ a.target) →
      ∃ g : M ≃ₜ N, ∃ W : Set M, IsOpen W ∧ K ∪ (⋃ p ∈ s, piece p) ⊆ W ∧
        IsLocalDiffeomorphOn planeModel planeModel ∞ g W := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ => ⟨h, V, hV, by simpa using hKV, hhV⟩
    | @insert p s _ ih =>
      intro hsa
      obtain ⟨g, W, hW, hsW, hgW⟩ := ih fun q hq => hsa q (Finset.mem_insert_of_mem hq)
      have hpa := hsa p (Finset.mem_insert_self p s)
      have hZ : IsCompact (K ∪ ⋃ q ∈ s, piece q) :=
        hK.union (s.isCompact_biUnion fun q hq => hpiece q (hsa q (Finset.mem_insert_of_mem hq)))
      obtain ⟨g', hg'⟩ := exists_smooth_on_simplex_keeping g a (hS p hpa).1 (hS p hpa).2.1
        (hS p hpa).2.2.1 hZ.isClosed hW hsW hgW
      refine ⟨g', {y | IsLocalDiffeomorphAt planeModel planeModel ∞ g' y},
        isOpen_setOf_isLocalDiffeomorphAt _ _ _ _, ?_, fun y => y.property⟩
      intro y hy
      rw [Finset.set_biUnion_insert] at hy
      apply hg' y
      rcases hy with hyK | hyp | hys
      · exact Or.inl (Or.inl hyK)
      · exact Or.inr hyp
      · exact Or.inl (Or.inr hys)
  obtain ⟨t, htD, hDt⟩ := hDc.elim_nhds_subcover (fun p => convexHull ℝ (S p : Set Plane))
    (fun p hp => (hS p (hDa hp)).2.2.2)
  obtain ⟨g, W, hW, hW', hgW⟩ := step t fun p hp => hDa (htD p hp)
  refine ⟨g, W, hW, ?_, hgW⟩
  rintro y (hyK | hyC)
  · exact hW' (Or.inl hyK)
  · obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp (hDt ⟨y, hyC, rfl⟩)
    exact hW' (Or.inr (mem_iUnion₂.mpr ⟨p, hp, a y, hyp, a.left_inv (hCa hyC)⟩))

/-- Homeomorphisms onto the explicit models can be smoothed. -/
theorem polynomialModelSmoothingStatement_holds : PolynomialModelSmoothingStatement.{u} := by
  apply polynomialModelSmoothing_of_chartStep
  intro M _ _ _ _ _ g _
  have : IsManifold planeModel ∞ (PolynomialLevel g) := polynomialLevel_isManifold g
  exact smoothingChartStep_holds

end R4Embedding
