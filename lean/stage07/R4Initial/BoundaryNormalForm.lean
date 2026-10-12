import R4CoS.LeanEval.ChallengeDeps
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import R4CoS.Moise.Brouwer
import R4Embedding.Problem

/-! Normal forms with holes have boundary points (part 1: combinatorics of the gluing).

When `n ≥ 1`, every point glued by the orientable or non-orientable normal-form relation
lies on the closed boundary arc `gluedArc L` with parameters in `[-1/L, 1 - 2/L]`. Interior
points of the disc and the open middle third of the first hole arc are therefore glued to
nothing: their classes are singletons. -/

noncomputable section
namespace R4Embedding

open Complex Set R4CoS.Topology.ClassificationOfSurfaces

theorem bdyPtOfReal_add_one (r : ℝ) :
    ClosedUnitDisc.bdyPtOfReal (r + 1) = ClosedUnitDisc.bdyPtOfReal r := by
  apply Subtype.ext
  change (Circle.exp (2 * Real.pi * (r + 1)) : ℂ) = (Circle.exp (2 * Real.pi * r) : ℂ)
  apply congrArg (fun z : Circle ↦ (z : ℂ))
  apply Circle.exp_eq_exp.mpr
  exact ⟨1, by push_cast; ring⟩

theorem continuous_bdyPtOfReal : Continuous ClosedUnitDisc.bdyPtOfReal :=
  Continuous.subtype_mk (continuous_subtype_val.comp Real.continuous_fourierChar) _

/-- The closed boundary arc that contains every glued point when some hole is present. -/
def gluedArc (L : ℝ) : Set ClosedUnitDisc :=
  ClosedUnitDisc.bdyPtOfReal '' Icc (-1 / L) (1 - 2 / L)

/-- Interior points together with the open middle third of the first hole arc. -/
def freeSet (L : ℝ) : Set ClosedUnitDisc := (gluedArc L)ᶜ

theorem isOpen_freeSet (L : ℝ) : IsOpen (freeSet L) :=
  ((isCompact_Icc.image continuous_bdyPtOfReal).isClosed).isOpen_compl

theorem mem_Icc_of_bounds {L a : ℝ} (hL : 0 < L) (h₁ : -1 ≤ a) (h₂ : a ≤ L - 2) :
    a / L ∈ Icc (-1 / L) (1 - 2 / L) := by
  constructor
  · exact div_le_div_of_nonneg_right h₁ hL.le
  · rw [show 1 - 2 / L = (L - 2) / L by field_simp]
    exact div_le_div_of_nonneg_right h₂ hL.le

theorem mem_gluedArc_of_bounds {L a : ℝ} (hL : 0 < L) (h₁ : -1 ≤ a) (h₂ : a ≤ L - 2) :
    ClosedUnitDisc.bdyPtOfReal (a / L) ∈ gluedArc L :=
  ⟨a / L, mem_Icc_of_bounds hL h₁ h₂, rfl⟩

/-- A negative parameter is moved into the arc by one full turn. -/
theorem mem_gluedArc_of_neg_bounds {L a : ℝ} (hL : 0 < L) (h₁ : a ≤ L + 1) (h₂ : 2 ≤ a) :
    ClosedUnitDisc.bdyPtOfReal (-a / L) ∈ gluedArc L := by
  refine ⟨(L - a) / L, mem_Icc_of_bounds hL (by linarith) (by linarith), ?_⟩
  rw [← bdyPtOfReal_add_one (-a / L)]
  congr 1
  field_simp
  ring

theorem eqvGen_eq_or_mem_gluedArc {R : ClosedUnitDisc → ClosedUnitDisc → Prop} {L : ℝ}
    (hR : ∀ x y, R x y → x ∈ gluedArc L ∧ y ∈ gluedArc L) {x y : ClosedUnitDisc}
    (h : Relation.EqvGen R x y) : x = y ∨ (x ∈ gluedArc L ∧ y ∈ gluedArc L) := by
  induction h with
  | rel x y hxy => exact Or.inr (hR x y hxy)
  | refl x => exact Or.inl rfl
  | symm x y _ ih =>
    rcases ih with h | ⟨h₁, h₂⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨h₂, h₁⟩
  | trans x y z _ _ ih₁ ih₂ =>
    rcases ih₁ with rfl | ⟨h₁, h₂⟩ <;> rcases ih₂ with rfl | ⟨h₃, h₄⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨h₃, h₄⟩
    · exact Or.inr ⟨h₁, h₂⟩
    · exact Or.inr ⟨h₁, h₄⟩

/-- Free points are glued to nothing. -/
theorem eq_of_eqvGen_of_mem_freeSet {R : ClosedUnitDisc → ClosedUnitDisc → Prop} {L : ℝ}
    (hR : ∀ x y, R x y → x ∈ gluedArc L ∧ y ∈ gluedArc L) {x y : ClosedUnitDisc}
    (hx : x ∈ freeSet L) (h : Relation.EqvGen R x y) : x = y :=
  (eqvGen_eq_or_mem_gluedArc hR h).resolve_right fun h' => hx h'.1

/-- The hole arcs `c` share their endpoint estimates in both normal forms. -/
theorem hole_endpoints_mem_gluedArc {L : ℝ} {n : ℕ} (hL : 0 < L) (hn : 3 * (n : ℝ) ≤ L)
    (x : Icc (0 : ℝ) 1) (i : Fin n) :
    ClosedUnitDisc.bdyPtOfReal (-(3 * (i : ℝ) + x) / L) ∈ gluedArc L ∧
      ClosedUnitDisc.bdyPtOfReal (-(3 * (i : ℝ) + 3 - x) / L) ∈ gluedArc L := by
  obtain ⟨hx₀, hx₁⟩ := x.2
  have hi : (i : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
  refine ⟨?_, mem_gluedArc_of_neg_bounds hL (by linarith) (by linarith)⟩
  by_cases hi₀ : (i : ℕ) = 0
  · have hi₀' : ((i : ℕ) : ℝ) = 0 := by exact_mod_cast hi₀
    rw [hi₀', mul_zero, zero_add, neg_div]
    rw [show -((x : ℝ) / L) = (-x) / L by ring]
    exact mem_gluedArc_of_bounds hL (by linarith) (by linarith)
  · have hi₁ : (1 : ℝ) ≤ i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi₀
    exact mem_gluedArc_of_neg_bounds hL (by linarith) (by linarith)

theorem orientableRel_mem_gluedArc {p n : ℕ} (hn : 1 ≤ n) {x y : ClosedUnitDisc}
    (h : OrientableRel p n x y) :
    x ∈ gluedArc (4 * p + 3 * n) ∧ y ∈ gluedArc (4 * p + 3 * n) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hL : (0 : ℝ) < 4 * p + 3 * n := by linarith
  rcases h with ⟨x, i⟩ | ⟨x, i⟩ | ⟨x, i⟩
  · obtain ⟨hx₀, hx₁⟩ := x.2
    have hi : (i : ℝ) + 1 ≤ p := by exact_mod_cast i.isLt
    exact ⟨mem_gluedArc_of_bounds hL (by linarith) (by linarith),
      mem_gluedArc_of_bounds hL (by linarith) (by linarith)⟩
  · obtain ⟨hx₀, hx₁⟩ := x.2
    have hi : (i : ℝ) + 1 ≤ p := by exact_mod_cast i.isLt
    exact ⟨mem_gluedArc_of_bounds hL (by linarith) (by linarith),
      mem_gluedArc_of_bounds hL (by linarith) (by linarith)⟩
  · exact hole_endpoints_mem_gluedArc hL (by linarith) x i

theorem nonOrientableRel_mem_gluedArc {p n : ℕ} (hn : 1 ≤ n) {x y : ClosedUnitDisc}
    (h : NonOrientableRel p n x y) :
    x ∈ gluedArc (2 * p + 3 * n) ∧ y ∈ gluedArc (2 * p + 3 * n) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hL : (0 : ℝ) < 2 * p + 3 * n := by linarith
  rcases h with ⟨x, i⟩ | ⟨x, i⟩
  · obtain ⟨hx₀, hx₁⟩ := x.2
    have hi : (i : ℝ) + 1 ≤ p := by exact_mod_cast i.isLt
    exact ⟨mem_gluedArc_of_bounds hL (by linarith) (by linarith),
      mem_gluedArc_of_bounds hL (by linarith) (by linarith)⟩
  · exact hole_endpoints_mem_gluedArc hL (by linarith) x i

section QuotientOnFree

variable {R : ClosedUnitDisc → ClosedUnitDisc → Prop} {L : ℝ}

/-- On the free set the quotient map is injective. -/
theorem quot_mk_injOn_freeSet (hR : ∀ x y, R x y → x ∈ gluedArc L ∧ y ∈ gluedArc L) :
    InjOn (Quot.mk R) (freeSet L) := fun _ hx _ _ hxy =>
  eq_of_eqvGen_of_mem_freeSet hR hx (Quot.eqvGen_exact hxy)

/-- Open subsets of the free set are saturated, so their images are open. -/
theorem isOpen_quot_mk_image (hR : ∀ x y, R x y → x ∈ gluedArc L ∧ y ∈ gluedArc L)
    {U : Set ClosedUnitDisc} (hU : IsOpen U) (hUF : U ⊆ freeSet L) :
    IsOpen (Quot.mk R '' U) := by
  apply isQuotientMap_quot_mk.isOpen_preimage.1
  convert hU using 1
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [← eq_of_eqvGen_of_mem_freeSet hR (hUF hx) (Quot.eqvGen_exact hxy)]
    exact hx
  · intro hy
    exact ⟨y, hy, rfl⟩

end QuotientOnFree

section Boundary

open R4CoS.Topology.ClassificationOfSurfaces.InvarianceOfDomain Filter Topology

/-- Invariance of domain, applied to the inverse: an embedded set carrying a continuous,
injective and open map into the plane is itself open in the plane. -/
theorem isOpen_image_of_isOpenMapOn {X : Type*} [TopologicalSpace X] {ι : X → Plane}
    (hι : IsEmbedding ι) {W : Set X} {Ψ : X → Plane}
    (hcont : ContinuousOn Ψ W) (hinj : InjOn Ψ W)
    (hopen : ∀ U ⊆ W, IsOpen U → IsOpen (Ψ '' U)) (hW : IsOpen W) :
    IsOpen (ι '' W) := by
  rcases W.eq_empty_or_nonempty with rfl | ⟨x₀, -⟩
  · simp
  have : Nonempty X := ⟨x₀⟩
  set G : Plane → Plane := fun y => ι (Function.invFunOn Ψ W y) with hGdef
  have hG : ∀ x ∈ W, G (Ψ x) = ι x := fun x hx => by
    simp only [hGdef]
    rw [hinj.leftInvOn_invFunOn hx]
  have himage : G '' (Ψ '' W) = ι '' W := by
    rw [image_image]
    exact image_congr hG
  rw [← himage]
  apply invariance_of_domain_open_map G (Ψ '' W) (hopen W subset_rfl hW)
  · rintro _ ⟨x, hx, rfl⟩
    have key : Tendsto (Function.invFunOn Ψ W) (𝓝[Ψ '' W] (Ψ x)) (𝓝 x) := by
      rw [(nhds_basis_opens x).tendsto_right_iff]
      rintro V ⟨hxV, hV⟩
      have hO : IsOpen (Ψ '' (V ∩ W)) := hopen _ inter_subset_right (hV.inter hW)
      filter_upwards [nhdsWithin_le_nhds (hO.mem_nhds ⟨x, ⟨hxV, hx⟩, rfl⟩)] with y hy
      obtain ⟨x', ⟨hx'V, hx'W⟩, rfl⟩ := hy
      rw [hinj.leftInvOn_invFunOn hx'W]
      exact hx'V
    show Tendsto G _ (𝓝 (G (Ψ x)))
    rw [hG x hx]
    exact (hι.continuous.tendsto x).comp key
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ h
    rw [hG x hx, hG x' hx'] at h
    rw [hι.injective h]

/-- An open subset of the plane inside the closed unit ball has no point of norm one. -/
theorem not_isOpen_of_norm_eq_one {S : Set Plane} (hS : S ⊆ Metric.closedBall 0 1)
    {p : Plane} (hp : p ∈ S) (hnorm : ‖p‖ = 1) : ¬ IsOpen S := by
  intro hO
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO p hp
  have hq : (1 + ε / 2) • p ∈ S := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, show (1 + ε / 2) • p - p = (ε / 2) • p by
      rw [add_smul, one_smul]; abel, norm_smul, hnorm, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    linarith
  have h := hS hq
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hnorm, Real.norm_eq_abs,
    abs_of_pos (by positivity)] at h
  linarith

/-- A free point on the boundary circle prevents a homeomorphism with a surface charted
on the plane: its neighbourhood would be an open subset of the plane inside the disc. -/
theorem isEmpty_homeomorph_quot_of_free_boundary {M : Type*} [TopologicalSpace M]
    [ChartedSpace Plane M] {R : ClosedUnitDisc → ClosedUnitDisc → Prop} {L : ℝ}
    (hR : ∀ x y, R x y → x ∈ gluedArc L ∧ y ∈ gluedArc L) {z₀ : ClosedUnitDisc}
    (hz₀ : z₀ ∈ freeSet L) (hnorm : ‖(z₀ : ℂ)‖ = 1) : IsEmpty (M ≃ₜ Quot R) := by
  refine ⟨fun h => ?_⟩
  let φ := chartAt Plane (h.symm (Quot.mk R z₀))
  let q : ClosedUnitDisc → M := fun z => h.symm (Quot.mk R z)
  have hq : Continuous q := h.symm.continuous.comp continuous_quot_mk
  let W : Set ClosedUnitDisc := freeSet L ∩ q ⁻¹' φ.source
  have hW : IsOpen W := (isOpen_freeSet L).inter (φ.open_source.preimage hq)
  have hz₀W : z₀ ∈ W := ⟨hz₀, mem_chart_source Plane _⟩
  let e := Complex.orthonormalBasisOneI.repr
  let ι : ClosedUnitDisc → Plane := fun z => e (z : ℂ)
  have hι : IsEmbedding ι := e.isometry.isEmbedding.comp IsEmbedding.subtypeVal
  have hopen : IsOpen (ι '' W) := by
    refine isOpen_image_of_isOpenMapOn (Ψ := fun z => φ (q z)) hι ?_ ?_ ?_ hW
    · exact φ.continuousOn.comp hq.continuousOn fun z hz => hz.2
    · intro x hx y hy hxy
      exact quot_mk_injOn_freeSet hR hx.1 hy.1 (h.symm.injective (φ.injOn hx.2 hy.2 hxy))
    · intro U hUW hU
      have h₁ : IsOpen (Quot.mk R '' U) := isOpen_quot_mk_image hR hU fun z hz => (hUW hz).1
      have h₂ : IsOpen (h.symm '' (Quot.mk R '' U)) := h.symm.isOpenMap _ h₁
      have h₃ := φ.isOpen_image_of_subset_source h₂ (by
        rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        exact (hUW hz).2)
      simpa only [image_image] using h₃
  refine not_isOpen_of_norm_eq_one (S := ι '' W) (p := ι z₀) ?_ ⟨z₀, hz₀W, rfl⟩ ?_ hopen
  · rintro _ ⟨z, -, rfl⟩
    have hz := z.2
    rw [Metric.mem_closedBall, dist_zero_right] at hz ⊢
    simpa [ι, LinearIsometryEquiv.norm_map] using hz
  · simpa [ι, LinearIsometryEquiv.norm_map] using hnorm

/-- The midpoint of the free middle third of the first hole arc. -/
theorem bdyPtOfReal_mem_freeSet {L : ℝ} (hL : 3 ≤ L) :
    ClosedUnitDisc.bdyPtOfReal (-3 / (2 * L)) ∈ freeSet L := by
  rintro ⟨r, ⟨hr₁, hr₂⟩, hEq⟩
  have hL0 : 0 < L := by linarith
  have hc : Circle.exp (2 * Real.pi * r) = Circle.exp (2 * Real.pi * (-3 / (2 * L))) := by
    have h := congrArg (fun z : ClosedUnitDisc => (z : ℂ)) hEq
    exact Circle.ext h
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 hc
  have hrm : r = -3 / (2 * L) + m := by
    have h2pi : (2 * Real.pi) ≠ 0 := by positivity
    apply mul_left_cancel₀ h2pi
    rw [hm]
    ring
  have hm₀ : (0 : ℝ) < m := by
    have h₁ : -1 / L ≤ -3 / (2 * L) + m := hrm ▸ hr₁
    have : -1 / L + 3 / (2 * L) = 1 / (2 * L) := by field_simp; ring
    have h₂ : (0 : ℝ) < 1 / (2 * L) := by positivity
    have h₃ : -3 / (2 * L) = -(3 / (2 * L)) := by ring
    linarith [show -1 / L ≤ -(3 / (2 * L)) + m by linarith]
  have hm₁ : (1 : ℝ) ≤ m := by exact_mod_cast (Int.cast_pos.1 hm₀ : (0 : ℤ) < m)
  have h₂ : -3 / (2 * L) + m ≤ 1 - 2 / L := hrm ▸ hr₂
  have : -3 / (2 * L) + 2 / L = 1 / (2 * L) := by field_simp; ring
  have h₃ : (0 : ℝ) < 1 / (2 * L) := by positivity
  linarith

/-- Normal forms with at least one hole are not homeomorphic to a surface charted on the
plane. This is the content of `NoBoundaryNormalFormStatement`. -/
theorem isEmpty_homeomorph_normalForm_of_hole (M : Type*) [TopologicalSpace M]
    [ChartedSpace Plane M] (p n : ℕ) (hn : 1 ≤ n) :
    IsEmpty (M ≃ₜ Quot (OrientableRel p n)) ∧ IsEmpty (M ≃ₜ Quot (NonOrientableRel p n)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  exact ⟨isEmpty_homeomorph_quot_of_free_boundary
      (fun _ _ h => orientableRel_mem_gluedArc hn h)
      (bdyPtOfReal_mem_freeSet (by linarith)) (Circle.norm_coe _),
    isEmpty_homeomorph_quot_of_free_boundary
      (fun _ _ h => nonOrientableRel_mem_gluedArc hn h)
      (bdyPtOfReal_mem_freeSet (by linarith)) (Circle.norm_coe _)⟩

end Boundary

end R4Embedding
