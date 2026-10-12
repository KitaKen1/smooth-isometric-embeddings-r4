import R4Initial.BoundaryNormalForm
import DifferentialGeometry.Topology.Manifold.Quotient
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.LocallyFinite

/-! The open Möbius band inside a non-orientable normal form.

The Möbius band is the quotient of the plane by the glide reflections
`(s, u) ↦ (s + n, (-1)ⁿ u)`; it is a smooth surface (Mathlib's charts on quotients by properly
discontinuous actions and qinz1yang's smooth structure on them). In the normal form
`a₁a₁⋯aₚaₚ`, the chords joining the first glued arc to the second, near their midpoints, close up
with a flip, because the two arcs are glued in the same direction. Sending the band onto these
chords is continuous and injective; by invariance of domain it is an open embedding into any
surface homeomorphic to the normal form. -/

noncomputable section
namespace R4Embedding

open Set Function Complex Filter Topology R4CoS.Topology.ClassificationOfSurfaces
open scoped Manifold ContDiff

/-! ### The deck group and the band -/

/-- The integers, written multiplicatively, as the deck group of the Möbius band. -/
def Glide : Type := Multiplicative ℤ

instance : Group Glide := inferInstanceAs (Group (Multiplicative ℤ))

namespace Glide

/-- The number of steps of a deck transformation. -/
def shift (g : Glide) : ℤ := Multiplicative.toAdd (g : Multiplicative ℤ)

/-- The deck transformation with a given number of steps. -/
def ofShift (n : ℤ) : Glide := Multiplicative.ofAdd n

theorem shift_one : shift 1 = 0 := rfl

theorem shift_mul (g h : Glide) : shift (g * h) = shift g + shift h := rfl

theorem shift_ofShift (n : ℤ) : shift (ofShift n) = n := rfl

theorem ofShift_shift (g : Glide) : ofShift (shift g) = g := rfl

theorem shift_injective : Injective shift := fun _ _ h => h

end Glide

/-- The linear part of the glide by `n` steps: the identity on the first coordinate and
`(-1)ⁿ` on the second. -/
def glideLinear (n : ℤ) : Plane →L[ℝ] Plane :=
  (EuclideanSpace.proj (0 : Fin 2)).smulRight (EuclideanSpace.single 0 1) +
    ((-1 : ℝ) ^ n) • (EuclideanSpace.proj (1 : Fin 2)).smulRight (EuclideanSpace.single 1 1)

/-- The glide reflection by `n` steps. -/
def glideMap (n : ℤ) (v : Plane) : Plane :=
  glideLinear n v + (n : ℝ) • EuclideanSpace.single 0 1

@[simp] theorem glideMap_apply_zero (n : ℤ) (v : Plane) : glideMap n v 0 = v 0 + n := by
  simp [glideMap, glideLinear]

@[simp] theorem glideMap_apply_one (n : ℤ) (v : Plane) :
    glideMap n v 1 = (-1 : ℝ) ^ n * v 1 := by
  simp [glideMap, glideLinear]

theorem plane_ext {v w : Plane} (h₀ : v 0 = w 0) (h₁ : v 1 = w 1) : v = w := by
  ext i
  fin_cases i
  · exact h₀
  · exact h₁

instance : MulAction Glide Plane where
  smul g v := glideMap (Glide.shift g) v
  one_smul v := by
    change glideMap 0 v = v
    exact plane_ext (by simp) (by simp)
  mul_smul g h v := by
    change glideMap (Glide.shift g + Glide.shift h) v =
      glideMap (Glide.shift g) (glideMap (Glide.shift h) v)
    refine plane_ext ?_ ?_
    · simp only [glideMap_apply_zero]
      push_cast
      ring
    · simp only [glideMap_apply_one, zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
      ring

theorem glide_smul_def (g : Glide) (v : Plane) : g • v = glideMap (Glide.shift g) v := rfl

theorem glide_smul_apply_zero (g : Glide) (v : Plane) : (g • v) 0 = v 0 + Glide.shift g :=
  glideMap_apply_zero _ _

theorem glide_smul_apply_one (g : Glide) (v : Plane) :
    (g • v) 1 = (-1 : ℝ) ^ Glide.shift g * v 1 :=
  glideMap_apply_one _ _

theorem continuous_coord (i : Fin 2) : Continuous fun v : Plane => v i :=
  (EuclideanSpace.proj i).continuous

instance : ContinuousConstSMul Glide Plane where
  continuous_const_smul g := (glideLinear (Glide.shift g)).continuous.add continuous_const

instance : ContMDiffConstSMul planeModel ∞ Glide Plane where
  contMDiff_const_smul g :=
    ((glideLinear (Glide.shift g)).contDiff.add contDiff_const).contMDiff

instance : IsCancelSMul Glide Plane where
  left_cancel' g v w h := by
    simpa using congrArg (fun x : Plane => g⁻¹ • x) h
  right_cancel' g h v hgh := by
    have h₀ := congrArg (fun x : Plane => x 0) hgh
    simp only [glide_smul_apply_zero, add_right_inj, Int.cast_inj] at h₀
    exact Glide.shift_injective h₀

instance : ProperlyDiscontinuousSMul Glide Plane where
  finite_disjoint_inter_image {K L} hK hL := by
    obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn (continuous_coord 0).continuousOn
    obtain ⟨B, hB⟩ := hL.exists_bound_of_continuousOn (continuous_coord 0).continuousOn
    apply ((Finset.Icc (-⌈A + B⌉) ⌈A + B⌉).finite_toSet.image Glide.ofShift).subset
    rintro g ⟨_, ⟨v, hv, rfl⟩, hvL⟩
    refine ⟨Glide.shift g, ?_, Glide.ofShift_shift g⟩
    have h₁ := hA v hv
    have h₂ := hB _ hvL
    simp only [glide_smul_apply_zero, Real.norm_eq_abs] at h₁ h₂
    have hn : |(Glide.shift g : ℝ)| ≤ A + B := by
      calc |(Glide.shift g : ℝ)| = |(v 0 + Glide.shift g) - v 0| := by ring_nf
        _ ≤ |v 0 + Glide.shift g| + |v 0| := abs_sub _ _
        _ ≤ A + B := by linarith
    obtain ⟨hn₁, hn₂⟩ := abs_le.mp hn
    have hc := Int.le_ceil (A + B)
    simp only [Finset.coe_Icc, mem_Icc]
    constructor
    · have h : ((-⌈A + B⌉ : ℤ) : ℝ) ≤ (Glide.shift g : ℝ) := by push_cast; linarith
      exact_mod_cast h
    · have h : ((Glide.shift g : ℤ) : ℝ) ≤ ((⌈A + B⌉ : ℤ) : ℝ) := by linarith
      exact_mod_cast h

/-- The open Möbius band. -/
abbrev MobiusBand := MulAction.orbitRel.Quotient Glide Plane

/-- The covering map of the band. -/
def mobiusMk : Plane → MobiusBand := Quotient.mk (MulAction.orbitRel Glide Plane)

theorem mobiusMk_smul (g : Glide) (v : Plane) : mobiusMk (g • v) = mobiusMk v :=
  Quotient.sound ⟨g, rfl⟩

theorem continuous_mobiusMk : Continuous mobiusMk := continuous_quot_mk

theorem mobiusMk_eq_iff {v w : Plane} : mobiusMk v = mobiusMk w ↔ ∃ g : Glide, g • w = v := by
  change Quotient.mk _ v = Quotient.mk _ w ↔ _
  rw [Quotient.eq]
  exact MulAction.mem_orbit_iff

/-! ### The band inside the normal form -/

section Band

variable (p : ℕ)

/-- The first glued arc, near its midpoint. -/
def bandStart (w : ℝ) : ℂ := ((ClosedUnitDisc.bdyPtOfReal ((1 / 2 + w / 4) / (2 * p))) : ℂ)

/-- The second glued arc, near its midpoint, traversed against the first. -/
def bandEnd (w : ℝ) : ℂ := ((ClosedUnitDisc.bdyPtOfReal ((1 + (1 / 2 - w / 4)) / (2 * p))) : ℂ)

theorem continuous_bandStart : Continuous (bandStart p) :=
  continuous_subtype_val.comp (continuous_bdyPtOfReal.comp
    ((continuous_const.add (continuous_id.div_const 4)).div_const _))

theorem continuous_bandEnd : Continuous (bandEnd p) :=
  continuous_subtype_val.comp (continuous_bdyPtOfReal.comp
    ((continuous_const.add (continuous_const.sub (continuous_id.div_const 4))).div_const _))

theorem norm_bdyPtOfReal (r : ℝ) : ‖((ClosedUnitDisc.bdyPtOfReal r : ClosedUnitDisc) : ℂ)‖ = 1 :=
  Circle.norm_coe _

theorem bandStart_mem (w : ℝ) : bandStart p w ∈ Metric.closedBall (0 : ℂ) 1 :=
  (ClosedUnitDisc.bdyPtOfReal _).2

theorem bandEnd_mem (w : ℝ) : bandEnd p w ∈ Metric.closedBall (0 : ℂ) 1 :=
  (ClosedUnitDisc.bdyPtOfReal _).2

/-- The point at position `t ∈ [0, 1]` (clamped) along the chord at transverse offset `w`. -/
def bandPoint (t w : ℝ) : ClosedUnitDisc :=
  ⟨((1 : ℝ) - projIcc (0 : ℝ) 1 zero_le_one t) • bandStart p w +
      ((projIcc (0 : ℝ) 1 zero_le_one t : ℝ)) • bandEnd p w,
    (convex_closedBall (0 : ℂ) 1) (bandStart_mem p w) (bandEnd_mem p w)
      (sub_nonneg.mpr (projIcc (0 : ℝ) 1 zero_le_one t).2.2) (projIcc (0 : ℝ) 1 zero_le_one t).2.1
      (by ring)⟩

theorem continuous_bandPoint : Continuous fun x : ℝ × ℝ => bandPoint p x.1 x.2 := by
  apply Continuous.subtype_mk
  have hc : Continuous fun x : ℝ × ℝ => (projIcc (0 : ℝ) 1 zero_le_one x.1 : ℝ) :=
    continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)
  exact ((continuous_const.sub hc).smul ((continuous_bandStart p).comp continuous_snd)).add
    (hc.smul ((continuous_bandEnd p).comp continuous_snd))

theorem bandPoint_zero (w : ℝ) : (bandPoint p 0 w : ℂ) = bandStart p w := by
  simp [bandPoint]

theorem bandPoint_one (w : ℝ) : (bandPoint p 1 w : ℂ) = bandEnd p w := by
  simp [bandPoint]

theorem bandPoint_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (w : ℝ) :
    (bandPoint p t w : ℂ) = ((1 : ℝ) - t) • bandStart p w + t • bandEnd p w := by
  simp [bandPoint, projIcc_of_mem _ ht]

variable {p}

/-- The end of each chord is glued to the start of the flipped chord. -/
theorem quot_bandPoint_one (hp : 1 ≤ p) {w : ℝ} (hw : |w| ≤ 2) :
    Quot.mk (NonOrientableRel p 0) (bandPoint p 1 w) =
      Quot.mk (NonOrientableRel p 0) (bandPoint p 0 (-w)) := by
  have hx : (1 / 2 - w / 4 : ℝ) ∈ Icc (0 : ℝ) 1 := by
    rw [abs_le] at hw
    constructor <;> linarith
  have hrel := NonOrientableRel.a (p := p) (n := 0) ⟨1 / 2 - w / 4, hx⟩ ⟨0, hp⟩
  have h₀ : bandPoint p 0 (-w) = ClosedUnitDisc.bdyPtOfReal ((2 * ((⟨0, hp⟩ : Fin p) : ℕ) +
      (1 / 2 - w / 4 : ℝ)) / (2 * p + 3 * ((0 : ℕ) : ℝ))) := by
    apply Subtype.ext
    rw [bandPoint_zero]
    simp only [bandStart, Nat.cast_zero, mul_zero, add_zero, zero_add]
    congr 3
    ring
  have h₁ : bandPoint p 1 w = ClosedUnitDisc.bdyPtOfReal ((2 * ((⟨0, hp⟩ : Fin p) : ℕ) + 1 +
      (1 / 2 - w / 4 : ℝ)) / (2 * p + 3 * ((0 : ℕ) : ℝ))) := by
    apply Subtype.ext
    rw [bandPoint_one]
    simp only [bandEnd, Nat.cast_zero, mul_zero, add_zero, zero_add]
  rw [h₀, h₁]
  exact (Quot.sound hrel).symm

/-- The transverse coordinate of the band, squeezed into `(-1, 1)`. -/
def bandWidth (u : ℝ) : ℝ := 2 / Real.pi * Real.arctan u

theorem continuous_bandWidth : Continuous bandWidth :=
  continuous_const.mul Real.continuous_arctan

theorem bandWidth_neg (u : ℝ) : bandWidth (-u) = -bandWidth u := by
  simp [bandWidth, Real.arctan_neg]

theorem abs_bandWidth_lt (u : ℝ) : |bandWidth u| < 1 := by
  have h₁ := Real.arctan_lt_pi_div_two u
  have h₂ := Real.neg_pi_div_two_lt_arctan u
  have hπ := Real.pi_pos
  rw [bandWidth, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / Real.pi)]
  have ha : |Real.arctan u| < Real.pi / 2 := abs_lt.mpr ⟨h₂, h₁⟩
  calc 2 / Real.pi * |Real.arctan u| < 2 / Real.pi * (Real.pi / 2) :=
        mul_lt_mul_of_pos_left ha (by positivity)
    _ = 1 := by field_simp

theorem bandWidth_injective : Injective bandWidth := by
  intro u v h
  have hπ : (2 / Real.pi) ≠ 0 := by positivity
  exact Real.arctan_injective (mul_left_cancel₀ hπ h)

theorem neg_one_zpow_mul_self (n : ℤ) : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by
  rw [← zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), ← two_mul, zpow_mul]
  norm_num

theorem bandWidth_neg_one_zpow_mul (n : ℤ) (u : ℝ) :
    bandWidth ((-1 : ℝ) ^ n * u) = (-1 : ℝ) ^ n * bandWidth u := by
  rcases Int.even_or_odd n with hn | hn
  · simp [hn.neg_one_zpow]
  · simp [hn.neg_one_zpow, bandWidth_neg]

/-! ### The band as a map from the plane -/

variable (p)

/-- The band as a map from its universal cover into the normal form. -/
def bandLift (v : Plane) : Quot (NonOrientableRel p 0) :=
  Quot.mk _ (bandPoint p (Int.fract (v 0)) ((-1 : ℝ) ^ ⌊v 0⌋ * bandWidth (v 1)))

theorem bandLift_smul (g : Glide) (v : Plane) : bandLift p (g • v) = bandLift p v := by
  have ht : Int.fract ((g • v) 0) = Int.fract (v 0) := by
    rw [glide_smul_apply_zero, Int.fract_add_intCast]
  have hw : (-1 : ℝ) ^ ⌊(g • v) 0⌋ * bandWidth ((g • v) 1) =
      (-1 : ℝ) ^ ⌊v 0⌋ * bandWidth (v 1) := by
    rw [glide_smul_apply_zero, glide_smul_apply_one, Int.floor_add_intCast,
      bandWidth_neg_one_zpow_mul, zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
    calc (-1 : ℝ) ^ ⌊v 0⌋ * (-1) ^ Glide.shift g * ((-1) ^ Glide.shift g * bandWidth (v 1)) =
        (-1 : ℝ) ^ ⌊v 0⌋ * ((-1) ^ Glide.shift g * (-1) ^ Glide.shift g) * bandWidth (v 1) := by
          ring
      _ = (-1 : ℝ) ^ ⌊v 0⌋ * bandWidth (v 1) := by rw [neg_one_zpow_mul_self, mul_one]
  simp only [bandLift, ht, hw]

/-- The closed strips `k ≤ s ≤ k + 1`. -/
def bandStrip (k : ℤ) : Set Plane := (fun v : Plane => v 0) ⁻¹' Icc (k : ℝ) (k + 1)

theorem locallyFinite_bandStrip : LocallyFinite bandStrip := by
  intro v
  refine ⟨(fun w : Plane => w 0) ⁻¹' Ioo (v 0 - 1) (v 0 + 1),
    ((continuous_coord 0).isOpen_preimage _ isOpen_Ioo).mem_nhds
      ⟨by linarith, by linarith⟩, ?_⟩
  apply (Set.finite_Icc (⌊v 0⌋ - 2) (⌊v 0⌋ + 2)).subset
  rintro k ⟨w, ⟨hw₁, hw₂⟩, hw₃, hw₄⟩
  have h₁ := Int.floor_le (v 0)
  have h₂ := Int.lt_floor_add_one (v 0)
  constructor
  · have h : ((⌊v 0⌋ - 2 : ℤ) : ℝ) < ((k + 1 : ℤ) : ℝ) := by push_cast; linarith
    have := Int.cast_lt.mp h
    omega
  · have h : ((k : ℤ) : ℝ) < ((⌊v 0⌋ + 2 : ℤ) : ℝ) := by push_cast; linarith
    have := Int.cast_lt.mp h
    omega

theorem abs_neg_one_zpow_mul_bandWidth_le (k : ℤ) (u : ℝ) :
    |(-1 : ℝ) ^ k * bandWidth u| ≤ 2 := by
  rw [abs_mul, abs_neg_one_zpow, one_mul]
  exact (abs_bandWidth_lt u).le.trans (by norm_num)

theorem bandLift_eqOn_strip (hp : 1 ≤ p) (k : ℤ) :
    EqOn (bandLift p) (fun v => Quot.mk (NonOrientableRel p 0)
      (bandPoint p (v 0 - k) ((-1 : ℝ) ^ k * bandWidth (v 1)))) (bandStrip k) := by
  intro v hv
  have hv₁ : (k : ℝ) ≤ v 0 := hv.1
  have hv₂ : v 0 ≤ k + 1 := hv.2
  rcases hv₂.lt_or_eq with hlt | heq
  · have hfl : ⌊v 0⌋ = k := Int.floor_eq_iff.mpr ⟨hv₁, hlt⟩
    simp only [bandLift, hfl, Int.fract]
  · have hfl : ⌊v 0⌋ = k + 1 := by rw [heq, Int.floor_add_one, Int.floor_intCast]
    have hfr : Int.fract (v 0) = 0 := by rw [heq, Int.fract_add_one, Int.fract_intCast]
    have h1 : v 0 - k = 1 := by rw [heq]; ring
    simp only [bandLift, hfl, hfr, h1]
    rw [quot_bandPoint_one hp (abs_neg_one_zpow_mul_bandWidth_le k (v 1)),
      zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]
    congr 2
    ring

theorem continuous_bandLift (hp : 1 ≤ p) : Continuous (bandLift p) := by
  refine locallyFinite_bandStrip.continuous ?_ (fun k => ?_) (fun k => ?_)
  · refine eq_univ_of_forall fun v => mem_iUnion.mpr ⟨⌊v 0⌋, ?_, ?_⟩
    · exact Int.floor_le _
    · exact (Int.lt_floor_add_one _).le
  · exact isClosed_Icc.preimage (continuous_coord 0)
  · refine ContinuousOn.congr ?_ (bandLift_eqOn_strip p hp k)
    exact (continuous_quot_mk.comp ((continuous_bandPoint p).comp
      (((continuous_coord 0).sub continuous_const).prodMk
        (continuous_const.mul (continuous_bandWidth.comp (continuous_coord 1)))))).continuousOn

/-- The band in the normal form. -/
def bandMap : MobiusBand → Quot (NonOrientableRel p 0) :=
  Quotient.lift (bandLift p) fun a b hab => by
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hab
    exact bandLift_smul p g b

theorem bandMap_mobiusMk (v : Plane) : bandMap p (mobiusMk v) = bandLift p v := rfl

theorem continuous_bandMap (hp : 1 ≤ p) : Continuous (bandMap p) :=
  (continuous_bandLift p hp).quotient_lift _

/-! ### Which points the normal form glues -/

variable {p}

theorem bdyPtOfReal_eq_iff {s t : ℝ} :
    ClosedUnitDisc.bdyPtOfReal s = ClosedUnitDisc.bdyPtOfReal t ↔ ∃ k : ℤ, s = t + k := by
  have key : ClosedUnitDisc.bdyPtOfReal s = ClosedUnitDisc.bdyPtOfReal t ↔
      Circle.exp (2 * Real.pi * s) = Circle.exp (2 * Real.pi * t) := by
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      exact Circle.ext h'
    · intro h
      exact Subtype.ext (congrArg (fun z : Circle => (z : ℂ)) h)
  rw [key, Circle.exp_eq_exp]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have h2 : (2 * Real.pi) * (s - (t + m)) = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (by positivity)
    · linarith
  · rintro ⟨m, rfl⟩
    exact ⟨m, by ring⟩

theorem norm_of_nonOrientableRel {n : ℕ} {x y : ClosedUnitDisc} (h : NonOrientableRel p n x y) :
    ‖(x : ℂ)‖ = 1 ∧ ‖(y : ℂ)‖ = 1 := by
  rcases h with ⟨x, i⟩ | ⟨x, i⟩ <;> exact ⟨norm_bdyPtOfReal _, norm_bdyPtOfReal _⟩

theorem eqvGen_mem_iff {α : Type*} {R : α → α → Prop} {S : Set α}
    (hS : ∀ a b, R a b → (a ∈ S ↔ b ∈ S)) {a b : α} (h : Relation.EqvGen R a b) :
    a ∈ S ↔ b ∈ S := by
  induction h with
  | rel a b hab => exact hS a b hab
  | refl => exact Iff.rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Interior points of the disc are glued to nothing. -/
theorem eq_of_eqvGen_of_norm_lt_one {z w : ClosedUnitDisc} (hz : ‖(z : ℂ)‖ < 1)
    (h : Relation.EqvGen (NonOrientableRel p 0) z w) : w = z := by
  have hS : ∀ a b, NonOrientableRel p 0 a b →
      (a ∈ ({z} : Set ClosedUnitDisc) ↔ b ∈ ({z} : Set ClosedUnitDisc)) := by
    intro a b hab
    have hn := norm_of_nonOrientableRel hab
    simp only [mem_singleton_iff]
    constructor
    · rintro rfl
      exact absurd hn.1 hz.ne
    · rintro rfl
      exact absurd hn.2 hz.ne
  exact (eqvGen_mem_iff hS h).mp rfl

theorem int_eq_zero_of_mul_bounds {k : ℤ} {L : ℝ} (hL : 1 ≤ L) (h₁ : -L < (k : ℝ) * L)
    (h₂ : (k : ℝ) * L < L) : k = 0 := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have hk' : (k : ℝ) + 1 ≤ 0 := by exact_mod_cast Int.add_one_le_of_lt hk
    nlinarith
  · exact hk
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith

theorem not_int_mul_bounds {k : ℤ} {L : ℝ} (hL : 1 ≤ L) (h₁ : 0 < (k : ℝ) * L)
    (h₂ : (k : ℝ) * L < L) : False := by
  rcases le_or_gt k 0 with hk | hk
  · have hk' : (k : ℝ) ≤ 0 := by exact_mod_cast hk
    nlinarith
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith

/-- A point inside the first glued arc is glued only to its partner on the second arc. -/
theorem eqvGen_firstArc (hp : 1 ≤ p) {s : ℝ} (hs₀ : 0 < s) (hs₁ : s < 1) {w : ClosedUnitDisc}
    (h : Relation.EqvGen (NonOrientableRel p 0) (ClosedUnitDisc.bdyPtOfReal (s / (2 * p))) w) :
    w = ClosedUnitDisc.bdyPtOfReal (s / (2 * p)) ∨
      w = ClosedUnitDisc.bdyPtOfReal ((1 + s) / (2 * p)) := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hL : (0 : ℝ) < 2 * p := by linarith
  have hL1 : (1 : ℝ) ≤ 2 * p := by linarith
  have hL2 : (2 : ℝ) ≤ 2 * p := by linarith
  have eq_iff : ∀ a b : ℝ, ClosedUnitDisc.bdyPtOfReal (a / (2 * p)) =
      ClosedUnitDisc.bdyPtOfReal (b / (2 * p)) → ∃ k : ℤ, a = b + k * (2 * p) := by
    intro a b hab
    obtain ⟨k, hk⟩ := bdyPtOfReal_eq_iff.mp hab
    refine ⟨k, ?_⟩
    field_simp at hk
    linarith
  let S : Set ClosedUnitDisc :=
    {ClosedUnitDisc.bdyPtOfReal (s / (2 * p)), ClosedUnitDisc.bdyPtOfReal ((1 + s) / (2 * p))}
  have hS : ∀ a b, NonOrientableRel p 0 a b → (a ∈ S ↔ b ∈ S) := by
    intro a b hab
    rcases hab with ⟨x, i⟩ | ⟨x, i⟩
    · obtain ⟨hx₀, hx₁⟩ := x.2
      have hi : (i : ℝ) + 1 ≤ p := by exact_mod_cast i.isLt
      have hi₀ : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
      simp only [S, Nat.cast_zero, mul_zero, add_zero, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro (h₁ | h₁)
        · obtain ⟨k, hk⟩ := eq_iff _ _ h₁
          have hk0 : k = 0 := int_eq_zero_of_mul_bounds hL1 (by linarith) (by linarith)
          subst hk0
          right
          congr 1
          push_cast at hk
          have hi0 : ((i : ℕ) : ℝ) = 0 := by
            have hlt : ((i : ℕ) : ℝ) < 1 := by linarith
            have : (i : ℕ) < 1 := by exact_mod_cast hlt
            simp [Nat.lt_one_iff.mp this]
          rw [hi0] at hk ⊢
          congr 1
          linarith
        · obtain ⟨k, hk⟩ := eq_iff _ _ h₁
          have hk0 : k = 0 := int_eq_zero_of_mul_bounds hL1 (by linarith) (by linarith)
          subst hk0
          push_cast at hk
          have hi1 : (1 : ℝ) ≤ ((i : ℕ) : ℝ) := by
            by_contra hcon
            have : (i : ℕ) < 1 := by exact_mod_cast (not_le.mp hcon)
            have : ((i : ℕ) : ℝ) = 0 := by simp [Nat.lt_one_iff.mp this]
            linarith
          exfalso
          linarith
      · rintro (h₁ | h₁)
        · obtain ⟨k, hk⟩ := eq_iff _ _ h₁
          exact (not_int_mul_bounds hL1 (by linarith) (by linarith)).elim
        · obtain ⟨k, hk⟩ := eq_iff _ _ h₁
          have hk0 : k = 0 := int_eq_zero_of_mul_bounds hL1 (by linarith) (by linarith)
          subst hk0
          push_cast at hk
          have hi0 : ((i : ℕ) : ℝ) = 0 := by
            have hlt : ((i : ℕ) : ℝ) < 1 := by linarith
            have : (i : ℕ) < 1 := by exact_mod_cast hlt
            simp [Nat.lt_one_iff.mp this]
          left
          rw [hi0] at hk ⊢
          congr 1
          congr 1
          linarith
    · exact i.elim0
  exact (eqvGen_mem_iff hS h).mp (Or.inl rfl)

theorem exists_int_of_bdyPtOfReal_div_eq {a b : ℝ}
    (h : ClosedUnitDisc.bdyPtOfReal (a / (2 * p)) = ClosedUnitDisc.bdyPtOfReal (b / (2 * p)))
    (hp : 1 ≤ p) : ∃ k : ℤ, a = b + k * (2 * p) := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  obtain ⟨k, hk⟩ := bdyPtOfReal_eq_iff.mp h
  refine ⟨k, ?_⟩
  have hL : (2 * p : ℝ) ≠ 0 := by positivity
  field_simp at hk
  linarith

/-! ### Injectivity of the chords -/

/-- The coordinate across the chords: projection onto the direction of angle `π / p`. -/
def bandHeight (z : ℂ) : ℝ := (z * Complex.exp (((-(Real.pi / p)) : ℝ) * Complex.I)).re

theorem bandHeight_bdy (r : ℝ) :
    bandHeight (p := p) (ClosedUnitDisc.bdyPtOfReal r : ℂ) =
      Real.cos (2 * Real.pi * r - Real.pi / p) := by
  have hb : ((ClosedUnitDisc.bdyPtOfReal r : ClosedUnitDisc) : ℂ) =
      Complex.exp (((2 * Real.pi * r : ℝ) : ℂ) * Complex.I) := rfl
  rw [bandHeight, hb, ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add,
    Complex.exp_ofReal_mul_I_re]
  congr 1

theorem bandHeight_combo (a b : ℝ) (A B : ℂ) :
    bandHeight (p := p) (a • A + b • B) = a * bandHeight (p := p) A + b * bandHeight (p := p) B := by
  simp only [bandHeight, add_mul, Complex.add_re, Complex.real_smul, mul_assoc,
    Complex.re_ofReal_mul]

theorem bandHeight_bandStart (hp : 1 ≤ p) (w : ℝ) :
    bandHeight (p := p) (bandStart p w) = Real.cos (Real.pi * (1 / 2 - w / 4) / p) := by
  have hp' : (p : ℝ) ≠ 0 := by positivity
  rw [bandStart, bandHeight_bdy, ← Real.cos_neg]
  congr 1
  field_simp
  ring

theorem bandHeight_bandEnd (hp : 1 ≤ p) (w : ℝ) :
    bandHeight (p := p) (bandEnd p w) = Real.cos (Real.pi * (1 / 2 - w / 4) / p) := by
  have hp' : (p : ℝ) ≠ 0 := by positivity
  rw [bandEnd, bandHeight_bdy]
  congr 1
  field_simp
  ring

theorem bandStart_ne_bandEnd (hp : 1 ≤ p) {w : ℝ} (hw : |w| < 2) :
    bandStart p w ≠ bandEnd p w := by
  intro h
  have h' : ClosedUnitDisc.bdyPtOfReal ((1 / 2 + w / 4) / (2 * p)) =
      ClosedUnitDisc.bdyPtOfReal ((1 + (1 / 2 - w / 4)) / (2 * p)) := Subtype.ext h
  obtain ⟨k, hk⟩ := exists_int_of_bdyPtOfReal_div_eq h' hp
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  rw [abs_lt] at hw
  have hk0 : k = 0 := int_eq_zero_of_mul_bounds (L := 2 * p) (by linarith) (by linarith)
    (by linarith)
  subst hk0
  push_cast at hk
  linarith

theorem norm_bandPoint_lt (hp : 1 ≤ p) {t w : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hw : |w| < 2) :
    ‖(bandPoint p t w : ℂ)‖ < 1 := by
  rw [bandPoint_of_mem p ⟨ht.1.le, ht.2.le⟩]
  exact norm_combo_lt_of_ne (by rw [bandStart, norm_bdyPtOfReal])
    (by rw [bandEnd, norm_bdyPtOfReal]) (bandStart_ne_bandEnd hp hw) (by linarith [ht.2]) ht.1
    (by ring)

theorem bandPoint_inj (hp : 1 ≤ p) {t t' w w' : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (ht' : t' ∈ Icc (0 : ℝ) 1) (hw : |w| < 2) (hw' : |w'| < 2)
    (h : bandPoint p t w = bandPoint p t' w') : t = t' ∧ w = w' := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hc := congrArg (fun z : ClosedUnitDisc => bandHeight (p := p) (z : ℂ)) h
  simp only [bandPoint_of_mem p ht, bandPoint_of_mem p ht', bandHeight_combo,
    bandHeight_bandStart hp, bandHeight_bandEnd hp] at hc
  set H := Real.cos (Real.pi * (1 / 2 - w / 4) / p)
  set H' := Real.cos (Real.pi * (1 / 2 - w' / 4) / p)
  have e1 : (1 - t) * H + t * H = H := by ring
  have e2 : (1 - t') * H' + t' * H' = H' := by ring
  rw [e1, e2] at hc
  have hθ : ∀ u : ℝ, |u| < 2 → Real.pi * (1 / 2 - u / 4) / p ∈ Icc 0 Real.pi := by
    intro u hu
    rw [abs_lt] at hu
    have hπ := Real.pi_pos
    constructor
    · apply div_nonneg _ (by linarith)
      nlinarith
    · rw [div_le_iff₀ (by linarith)]
      nlinarith
  have hθeq := Real.injOn_cos (hθ w hw) (hθ w' hw') hc
  have hpne : (p : ℝ) ≠ 0 := by positivity
  rw [div_left_inj' hpne] at hθeq
  have hww : w = w' := by
    have := mul_left_cancel₀ Real.pi_pos.ne' hθeq
    linarith
  subst hww
  refine ⟨?_, rfl⟩
  have hval := congrArg Subtype.val h
  simp only [bandPoint_of_mem p ht, bandPoint_of_mem p ht', Complex.real_smul] at hval
  have hz : ((t - t' : ℝ) : ℂ) * (bandEnd p w - bandStart p w) = 0 := by
    push_cast at hval ⊢
    linear_combination hval
  rcases mul_eq_zero.mp hz with h0 | h0
  · exact sub_eq_zero.mp (Complex.ofReal_eq_zero.mp h0)
  · exact absurd (sub_eq_zero.mp h0).symm (bandStart_ne_bandEnd hp hw)

/-! ### Injectivity of the band -/

theorem exists_normal_rep (x : MobiusBand) : ∃ v : Plane, mobiusMk v = x ∧ 0 ≤ v 0 ∧ v 0 < 1 := by
  induction x using Quotient.inductionOn with
  | h v =>
    refine ⟨Glide.ofShift (-⌊v 0⌋) • v, mobiusMk_smul _ _, ?_, ?_⟩
    · rw [glide_smul_apply_zero, Glide.shift_ofShift]
      push_cast
      linarith [Int.floor_le (v 0)]
    · rw [glide_smul_apply_zero, Glide.shift_ofShift]
      push_cast
      linarith [Int.lt_floor_add_one (v 0)]

theorem bandMap_injective (hp : 1 ≤ p) : Injective (bandMap p) := by
  intro x y hxy
  obtain ⟨v, rfl, hv₀, hv₁⟩ := exists_normal_rep x
  obtain ⟨v', rfl, hv'₀, hv'₁⟩ := exists_normal_rep y
  rw [bandMap_mobiusMk, bandMap_mobiusMk] at hxy
  have hfl : ⌊v 0⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hv₀, hv₁⟩
  have hfl' : ⌊v' 0⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hv'₀, hv'₁⟩
  have hfr : Int.fract (v 0) = v 0 := Int.fract_eq_self.mpr ⟨hv₀, hv₁⟩
  have hfr' : Int.fract (v' 0) = v' 0 := Int.fract_eq_self.mpr ⟨hv'₀, hv'₁⟩
  simp only [bandLift, hfl, hfl', hfr, hfr', zpow_zero, one_mul] at hxy
  have hE := Quot.eqvGen_exact hxy
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hW := abs_bandWidth_lt (v 1)
  have hW' := abs_bandWidth_lt (v' 1)
  have hW2 : |bandWidth (v 1)| < 2 := hW.trans (by norm_num)
  have hW2' : |bandWidth (v' 1)| < 2 := hW'.trans (by norm_num)
  suffices hvv : v = v' by rw [hvv]
  rcases hv₀.lt_or_eq with hpos | hzero
  · have hint := norm_bandPoint_lt hp ⟨hpos, hv₁⟩ hW2
    have heq := eq_of_eqvGen_of_norm_lt_one hint hE
    obtain ⟨h1, h2⟩ := bandPoint_inj hp ⟨hv'₀, hv'₁.le⟩ ⟨hv₀, hv₁.le⟩ hW2' hW2 heq
    exact plane_ext h1.symm (bandWidth_injective h2.symm)
  · rcases hv'₀.lt_or_eq with hpos' | hzero'
    · exfalso
      have hint' := norm_bandPoint_lt hp ⟨hpos', hv'₁⟩ hW2'
      have heq := eq_of_eqvGen_of_norm_lt_one hint' (Relation.EqvGen.symm _ _ hE)
      have hn : ‖((bandPoint p (v 0) (bandWidth (v 1)) : ClosedUnitDisc) : ℂ)‖ = 1 := by
        rw [← hzero, bandPoint_zero, bandStart, norm_bdyPtOfReal]
      rw [heq] at hn
      linarith
    · have hs : ∀ u : ℝ, bandPoint p 0 u =
          ClosedUnitDisc.bdyPtOfReal ((1 / 2 + u / 4) / (2 * p)) := fun u =>
        Subtype.ext (bandPoint_zero p u)
      rw [← hzero, ← hzero', hs, hs] at hE
      rw [abs_lt] at hW hW'
      rcases eqvGen_firstArc hp (s := 1 / 2 + bandWidth (v 1) / 4) (by linarith) (by linarith)
        hE with h₁ | h₁
      · obtain ⟨k, hk⟩ := exists_int_of_bdyPtOfReal_div_eq h₁ hp
        have hk0 : k = 0 := int_eq_zero_of_mul_bounds (L := 2 * p) (by linarith) (by linarith)
          (by linarith)
        subst hk0
        push_cast at hk
        exact plane_ext (by linarith) (bandWidth_injective (by linarith))
      · obtain ⟨k, hk⟩ := exists_int_of_bdyPtOfReal_div_eq h₁ hp
        have hk0 : k = 0 := int_eq_zero_of_mul_bounds (L := 2 * p) (by linarith) (by linarith)
          (by linarith)
        subst hk0
        push_cast at hk
        exfalso
        linarith

end Band

/-! ### Invariance of domain and the open embedding -/

section Domain

open R4CoS.Topology.ClassificationOfSurfaces.InvarianceOfDomain

/-- Invariance of domain for surfaces charted on the plane: a continuous injective map is
open. -/
theorem isOpenMap_of_continuous_injective {X Y : Type*} [TopologicalSpace X]
    [ChartedSpace Plane X] [TopologicalSpace Y] [ChartedSpace Plane Y] {f : X → Y}
    (hf : Continuous f) (hinj : Injective f) : IsOpenMap f := by
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hxU, rfl⟩
  set φ := chartAt Plane x
  set χ := chartAt Plane (f x)
  let W : Set Plane := φ.target ∩ φ.symm ⁻¹' (U ∩ f ⁻¹' χ.source)
  have hW : IsOpen W := φ.isOpen_inter_preimage_symm (hU.inter (χ.open_source.preimage hf))
  let G : Plane → Plane := fun z => χ (f (φ.symm z))
  have hGc : ContinuousOn G W := by
    refine χ.continuousOn.comp (hf.comp_continuousOn (φ.continuousOn_symm.mono
      inter_subset_left)) ?_
    intro z hz
    exact hz.2.2
  have hGi : InjOn G W := by
    intro z hz z' hz' h
    exact φ.symm.injOn hz.1 hz'.1 (hinj (χ.injOn hz.2.2 hz'.2.2 h))
  have hGW : IsOpen (G '' W) := invariance_of_domain_open_map G W hW hGc hGi
  have hGt : G '' W ⊆ χ.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact χ.map_source hz.2.2
  have hopen : IsOpen (χ.symm '' (G '' W)) := χ.symm.isOpen_image_of_subset_source hGW hGt
  have hsub : χ.symm '' (G '' W) ⊆ f '' U := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨φ.symm z, hz.2.1, (χ.left_inv hz.2.2).symm⟩
  have hx : φ x ∈ W := by
    refine ⟨φ.map_source (mem_chart_source Plane x), ?_⟩
    rw [mem_preimage, φ.left_inv (mem_chart_source Plane x)]
    exact ⟨hxU, mem_chart_source Plane (f x)⟩
  have hmem : f x ∈ χ.symm '' (G '' W) := by
    refine ⟨G (φ x), ⟨φ x, hx, rfl⟩, ?_⟩
    simp only [G, φ.left_inv (mem_chart_source Plane x)]
    exact χ.left_inv (mem_chart_source Plane (f x))
  exact Filter.mem_of_superset (hopen.mem_nhds hmem) hsub

/-- A surface homeomorphic to a non-orientable closed normal form contains an open Möbius
band. -/
theorem exists_isOpenEmbedding_mobiusBand {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
    {p : ℕ} (hp : 1 ≤ p) (h : M ≃ₜ Quot (NonOrientableRel p 0)) :
    ∃ f : MobiusBand → M, IsOpenEmbedding f := by
  have hc : Continuous (h.symm ∘ bandMap p) := h.symm.continuous.comp (continuous_bandMap p hp)
  have hi : Injective (h.symm ∘ bandMap p) := h.symm.injective.comp (bandMap_injective hp)
  exact ⟨_, IsOpenEmbedding.of_continuous_injective_isOpenMap hc hi
    (isOpenMap_of_continuous_injective hc hi)⟩

end Domain

end R4Embedding
