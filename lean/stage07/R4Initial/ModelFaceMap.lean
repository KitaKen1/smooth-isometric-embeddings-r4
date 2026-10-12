import R4Embedding.PolynomialDouble
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Stage 07d(B), geometric half, part 1: the horizontal coordinate of the face maps.

The `x`-axis cut points of the planar model are `x_0 = −R`, `x_{2i+1} = 3(i+1) − 1`,
`x_{2i+2} = 3(i+1) + 1` (the ends of the `i`-th hole) and `x_{2g+1} = R`. The map `τ` is the
piecewise linear map `[0, 2g+1] → [−R, R]` sending `k` to `x_k`, written as a sum of ramps, and
`X u = τ((2g+1)/π · arccos(−u))` is the horizontal coordinate of the face maps: on the boundary
circle, the arc of angles `[π(2g+1+k+t)/(2g+1)]`, `t ∈ [0,1]`, has `X = x_k + t (x_{k+1} − x_k)`. -/

noncomputable section
namespace R4Embedding
namespace ModelFace

open Real Finset

variable (g : ℕ)

/-! ### Cut points -/

/-- The cut points on the `x`-axis. -/
def node (k : ℕ) : ℝ :=
  if k = 0 then -modelRadius g
  else if k = 2 * g + 1 then modelRadius g
  else if k % 2 = 1 then 3 * (((k + 1) / 2 : ℕ) : ℝ) - 1
  else 3 * ((k / 2 : ℕ) : ℝ) + 1

theorem node_zero : node g 0 = -modelRadius g := by
  simp [node]

theorem node_last : node g (2 * g + 1) = modelRadius g := by
  simp [node]

theorem node_left {i : ℕ} (hi : i < g) : node g (2 * i + 1) = 3 * ((i : ℝ) + 1) - 1 := by
  have h1 : 2 * i + 1 ≠ 0 := by omega
  have h2 : 2 * i + 1 ≠ 2 * g + 1 := by omega
  have h3 : (2 * i + 1) % 2 = 1 := by omega
  have h4 : (2 * i + 1 + 1) / 2 = i + 1 := by omega
  simp only [node, h1, h2, h3, h4, ite_false, ite_true]
  push_cast
  ring

theorem node_right {i : ℕ} (hi : i < g) : node g (2 * i + 2) = 3 * ((i : ℝ) + 1) + 1 := by
  have h1 : 2 * i + 2 ≠ 0 := by omega
  have h2 : 2 * i + 2 ≠ 2 * g + 1 := by omega
  have h3 : ¬ (2 * i + 2) % 2 = 1 := by omega
  have h4 : (2 * i + 2) / 2 = i + 1 := by omega
  simp only [node, h1, h2, h3, h4, ite_false]
  push_cast
  ring

theorem modelRadius_eq : modelRadius g = 3 * ((g : ℝ) + 1) := rfl

theorem node_lt_succ {k : ℕ} (hk : k ≤ 2 * g) : node g k < node g (k + 1) := by
  have hR := modelRadius_pos g
  rcases Nat.even_or_odd' k with ⟨i, rfl | rfl⟩
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [show 2 * 0 + 1 = 1 by rfl, show 2 * 0 = 0 by rfl, node_zero]
      rcases Nat.eq_zero_or_pos g with rfl | hg
      · rw [show (1 : ℕ) = 2 * 0 + 1 by rfl, node_last]
        linarith
      · rw [show (1 : ℕ) = 2 * 0 + 1 by rfl, node_left g hg]
        rw [modelRadius_eq]
        push_cast
        nlinarith
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [show 2 * (i' + 1) = 2 * i' + 2 by ring, node_right g (by omega)]
      by_cases hlast : 2 * i' + 2 + 1 = 2 * g + 1
      · rw [hlast, node_last, modelRadius_eq]
        have : (i' : ℝ) + 1 + 1 = (g : ℝ) + 1 := by
          have : i' + 1 = g := by omega
          rw [← this]
          push_cast
          ring
        nlinarith
      · rw [show 2 * i' + 2 + 1 = 2 * (i' + 1) + 1 by ring, node_left g (by omega)]
        push_cast
        linarith
  · rw [show 2 * i + 1 + 1 = 2 * i + 2 by ring, node_left g (by omega), node_right g (by omega)]
    linarith

theorem node_mono {k k' : ℕ} (hkk' : k ≤ k') (hk' : k' ≤ 2 * g + 1) : node g k ≤ node g k' := by
  induction k' with
  | zero =>
    obtain rfl : k = 0 := by omega
    exact le_rfl
  | succ m ih =>
    rcases Nat.lt_or_ge k (m + 1) with h | h
    · exact (ih (by omega) (by omega)).trans (node_lt_succ g (by omega)).le
    · obtain rfl : k = m + 1 := by omega
      exact le_rfl

/-! ### Ramps and the piecewise linear map `τ` -/

/-- The clamp of a real number to `[0, 1]`. -/
def clamp01 (s : ℝ) : ℝ := max 0 (min s 1)

theorem clamp01_of_one_le {s : ℝ} (h : 1 ≤ s) : clamp01 s = 1 := by
  simp [clamp01, min_eq_right h]

theorem clamp01_of_nonpos {s : ℝ} (h : s ≤ 0) : clamp01 s = 0 := by
  simp only [clamp01]
  exact max_eq_left ((min_le_left _ _).trans h)

theorem clamp01_of_mem {s : ℝ} (h₀ : 0 ≤ s) (h₁ : s ≤ 1) : clamp01 s = s := by
  simp [clamp01, min_eq_left h₁, max_eq_right h₀]

theorem continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_id.min continuous_const)

theorem monotone_clamp01 : Monotone clamp01 := fun _ _ h =>
  max_le_max le_rfl (min_le_min h le_rfl)

theorem clamp01_lt {s s' : ℝ} (h₀ : 0 ≤ s) (h₁ : s < 1) (h : s < s') :
    clamp01 s < clamp01 s' := by
  rw [clamp01_of_mem h₀ h₁.le]
  simp only [clamp01]
  exact lt_max_of_lt_right (lt_min h h₁)

/-- The piecewise linear map sending `k` to the `k`-th cut point. -/
def tau (a : ℝ) : ℝ :=
  node g 0 + ∑ k ∈ range (2 * g + 1), (node g (k + 1) - node g k) * clamp01 (a - k)

theorem continuous_tau : Continuous (tau g) := by
  unfold tau
  exact continuous_const.add (continuous_finset_sum _ fun k _ =>
    continuous_const.mul (continuous_clamp01.comp (continuous_id.sub continuous_const)))

theorem tau_piece {m : ℕ} (hm : m ≤ 2 * g) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    tau g (m + t) = node g m + t * (node g (m + 1) - node g m) := by
  unfold tau
  have hsplit : range (2 * g + 1) = range m ∪ ({m} ∪ Ico (m + 1) (2 * g + 1)) := by
    ext k
    simp only [mem_range, mem_union, mem_singleton, mem_Ico]
    omega
  rw [hsplit, sum_union, sum_union, sum_singleton]
  · have hlow : ∑ k ∈ range m, (node g (k + 1) - node g k) * clamp01 ((m : ℝ) + t - k) =
        ∑ k ∈ range m, (node g (k + 1) - node g k) := by
      refine sum_congr rfl fun k hk => ?_
      rw [clamp01_of_one_le, mul_one]
      have : (k : ℝ) + 1 ≤ m := by exact_mod_cast mem_range.mp hk
      linarith
    have hhigh : ∑ k ∈ Ico (m + 1) (2 * g + 1),
        (node g (k + 1) - node g k) * clamp01 ((m : ℝ) + t - k) = 0 := by
      refine sum_eq_zero fun k hk => ?_
      rw [clamp01_of_nonpos, mul_zero]
      have : (m : ℝ) + 1 ≤ k := by exact_mod_cast (mem_Ico.mp hk).1
      linarith
    rw [hlow, hhigh, sum_range_sub (node g), show (m : ℝ) + t - m = t by ring,
      clamp01_of_mem ht₀ ht₁]
    ring
  · rw [disjoint_singleton_left]
    simp
  · rw [disjoint_union_right, disjoint_singleton_right]
    refine ⟨by simp, ?_⟩
    rw [disjoint_left]
    intro k hk hk'
    simp only [mem_range] at hk
    simp only [mem_Ico] at hk'
    omega

theorem tau_nat {m : ℕ} (hm : m ≤ 2 * g + 1) : tau g m = node g m := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simpa using tau_piece g (Nat.zero_le _) le_rfl zero_le_one
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have := tau_piece g (m := m') (by omega) zero_le_one le_rfl
    push_cast
    rw [this]
    ring

theorem monotone_tau : Monotone (tau g) := by
  intro a b hab
  unfold tau
  rw [add_le_add_iff_left]
  refine sum_le_sum fun k hk => ?_
  refine mul_le_mul_of_nonneg_left (monotone_clamp01 (by linarith)) ?_
  exact (sub_pos.mpr (node_lt_succ g (by simp at hk; omega))).le

theorem tau_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 2 * g + 1) :
    tau g a < tau g b := by
  unfold tau
  rw [add_lt_add_iff_left]
  set k₀ := ⌊a⌋₊ with hk₀
  have hk₀a : (k₀ : ℝ) ≤ a := Nat.floor_le ha
  have hak₀ : a < k₀ + 1 := Nat.lt_floor_add_one a
  have hk₀lt : k₀ < 2 * g + 1 := by
    have : (k₀ : ℝ) < 2 * g + 1 := by linarith
    exact_mod_cast this
  have hterm : ∀ k ∈ range (2 * g + 1),
      (node g (k + 1) - node g k) * clamp01 (a - k) ≤
        (node g (k + 1) - node g k) * clamp01 (b - k) := fun k hk =>
    mul_le_mul_of_nonneg_left (monotone_clamp01 (by linarith))
      (sub_pos.mpr (node_lt_succ g (by simp at hk; omega))).le
  rw [← sub_pos, ← sum_sub_distrib]
  have hpos : 0 < (node g (k₀ + 1) - node g k₀) * clamp01 (b - k₀) -
      (node g (k₀ + 1) - node g k₀) * clamp01 (a - k₀) := by
    rw [← mul_sub]
    exact mul_pos (sub_pos.mpr (node_lt_succ g (by omega)))
      (sub_pos.mpr (clamp01_lt (by linarith) (by linarith) (by linarith)))
  refine hpos.trans_le ?_
  exact single_le_sum (f := fun k => (node g (k + 1) - node g k) * clamp01 (b - k) -
      (node g (k + 1) - node g k) * clamp01 (a - k))
    (fun k hk => sub_nonneg.mpr (hterm k hk)) (mem_range.mpr hk₀lt)

theorem strictMonoOn_tau : StrictMonoOn (tau g) (Set.Icc 0 (2 * g + 1)) :=
  fun _ ha _ hb hab => tau_lt g ha.1 hab hb.2

/-! ### The angle parameter and the horizontal coordinate -/

/-- The boundary angle parameter: `a u ∈ [0, 2g+1]` measures the angle `arccos(−u)` in units of
`π/(2g+1)`. -/
def angleParam (u : ℝ) : ℝ := (2 * g + 1) / π * arccos (-u)

theorem continuous_angleParam : Continuous (angleParam g) :=
  continuous_const.mul (continuous_arccos.comp continuous_neg)

theorem angleParam_nonneg (u : ℝ) : 0 ≤ angleParam g u :=
  mul_nonneg (div_nonneg (by positivity) pi_pos.le) (arccos_nonneg _)

theorem angleParam_le (u : ℝ) : angleParam g u ≤ 2 * g + 1 := by
  unfold angleParam
  rw [div_mul_eq_mul_div, div_le_iff₀ pi_pos]
  exact mul_le_mul_of_nonneg_left (arccos_le_pi _) (by positivity)

theorem angleParam_neg_one : angleParam g (-1) = 0 := by
  simp [angleParam]

theorem angleParam_one : angleParam g 1 = 2 * g + 1 := by
  simp [angleParam, pi_ne_zero]

theorem strictMonoOn_angleParam : StrictMonoOn (angleParam g) (Set.Icc (-1) 1) := by
  intro u hu u' hu' huu'
  unfold angleParam
  refine mul_lt_mul_of_pos_left ?_ (div_pos (by positivity) pi_pos)
  exact strictAntiOn_arccos ⟨by linarith [hu'.2], by linarith [hu'.1]⟩
    ⟨by linarith [hu.2], by linarith [hu.1]⟩ (by linarith)

/-- The horizontal coordinate of the face maps. -/
def horiz (u : ℝ) : ℝ := tau g (angleParam g u)

theorem continuous_horiz : Continuous (horiz g) :=
  (continuous_tau g).comp (continuous_angleParam g)

theorem strictMonoOn_horiz : StrictMonoOn (horiz g) (Set.Icc (-1) 1) := fun u hu u' hu' h =>
  tau_lt g (angleParam_nonneg g u) (strictMonoOn_angleParam g hu hu' h) (angleParam_le g u')

theorem horiz_neg_one : horiz g (-1) = -modelRadius g := by
  rw [horiz, angleParam_neg_one, show (0 : ℝ) = ((0 : ℕ) : ℝ) by simp,
    tau_nat g (Nat.zero_le _), node_zero]

theorem horiz_one : horiz g 1 = modelRadius g := by
  rw [horiz, angleParam_one, show (2 * g + 1 : ℝ) = ((2 * g + 1 : ℕ) : ℝ) by push_cast; ring,
    tau_nat g le_rfl, node_last]

theorem horiz_mem (u : ℝ) : horiz g u ∈ Set.Icc (-modelRadius g) (modelRadius g) := by
  constructor
  · rw [← node_zero, ← tau_nat g (Nat.zero_le _)]
    exact monotone_tau g (by simpa using angleParam_nonneg g u)
  · rw [← node_last, ← tau_nat g le_rfl]
    exact monotone_tau g (by push_cast; exact angleParam_le g u)

/-! ### The vertical coordinate -/

/-- The outer semicircle `√(R² − x²)`. -/
def outerH (x : ℝ) : ℝ := √(modelRadius g ^ 2 - x ^ 2)

/-- The hole semicircles; at most one term is nonzero. -/
def holeH (x : ℝ) : ℝ := ∑ i ∈ range g, √(1 - (x - 3 * ((i : ℝ) + 1)) ^ 2)

theorem continuous_outerH : Continuous (outerH g) :=
  continuous_sqrt.comp (continuous_const.sub (continuous_pow 2))

theorem continuous_holeH : Continuous (holeH g) :=
  continuous_finset_sum _ fun _ _ =>
    continuous_sqrt.comp (continuous_const.sub ((continuous_id.sub continuous_const).pow 2))

theorem holeH_nonneg (x : ℝ) : 0 ≤ holeH g x := sum_nonneg fun _ _ => sqrt_nonneg _

theorem outerH_nonneg (x : ℝ) : 0 ≤ outerH g x := sqrt_nonneg _

theorem hole_term_eq_zero {x c : ℝ} (h : 1 ≤ |x - c|) : √(1 - (x - c) ^ 2) = 0 := by
  rw [sqrt_eq_zero']
  nlinarith [sq_abs (x - c), abs_nonneg (x - c)]

theorem holeH_eq_term {x : ℝ} {i : ℕ} (hi : i < g) (hx : |x - 3 * ((i : ℝ) + 1)| ≤ 1) :
    holeH g x = √(1 - (x - 3 * ((i : ℝ) + 1)) ^ 2) := by
  unfold holeH
  rw [sum_eq_single i]
  · intro j _ hji
    apply hole_term_eq_zero
    rw [abs_le] at hx
    rcases lt_or_gt_of_ne hji with h | h
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt h
      exact le_trans (by linarith [hx.1]) (le_abs_self _)
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt h
      exact le_trans (by linarith [hx.2]) (neg_le_abs _)
  · intro hi'
    exact absurd (mem_range.mpr hi) hi'

theorem holeH_eq_zero {x : ℝ} (hx : ∀ i < g, 1 ≤ |x - 3 * ((i : ℝ) + 1)|) : holeH g x = 0 :=
  sum_eq_zero fun i hi => hole_term_eq_zero (hx i (mem_range.mp hi))

theorem holeH_le_one (x : ℝ) : holeH g x ≤ 1 := by
  by_cases h : ∃ i < g, |x - 3 * ((i : ℝ) + 1)| ≤ 1
  · obtain ⟨i, hi, hx⟩ := h
    rw [holeH_eq_term g hi hx, sqrt_le_left zero_le_one]
    nlinarith [sq_nonneg (x - 3 * ((i : ℝ) + 1))]
  · push_neg at h
    rw [holeH_eq_zero g fun i hi => (h i hi).le]
    exact zero_le_one

theorem holeH_le_iff {x y : ℝ} (hy : 0 ≤ y) :
    holeH g x ≤ y ↔ ∀ i < g, 1 ≤ (x - 3 * ((i : ℝ) + 1)) ^ 2 + y ^ 2 := by
  constructor
  · intro h i hi
    by_cases hx : |x - 3 * ((i : ℝ) + 1)| ≤ 1
    · rw [holeH_eq_term g hi hx, sqrt_le_left hy] at h
      linarith
    · push_neg at hx
      nlinarith [sq_abs (x - 3 * ((i : ℝ) + 1)), sq_nonneg y]
  · intro h
    by_cases hx : ∃ i < g, |x - 3 * ((i : ℝ) + 1)| ≤ 1
    · obtain ⟨i, hi, hx⟩ := hx
      rw [holeH_eq_term g hi hx, sqrt_le_left hy]
      linarith [h i hi]
    · push_neg at hx
      rw [holeH_eq_zero g fun i hi => (hx i hi).le]
      exact hy

theorem le_outerH_iff {x y : ℝ} (hy : 0 ≤ y) (hx : x ^ 2 ≤ modelRadius g ^ 2) :
    y ≤ outerH g x ↔ x ^ 2 + y ^ 2 ≤ modelRadius g ^ 2 := by
  unfold outerH
  rw [le_sqrt hy (by linarith)]
  constructor <;> intro h <;> linarith

theorem holeH_of_abs_ge {x : ℝ} (hx : 3 * (g : ℝ) + 2 ≤ |x|) : holeH g x = 0 := by
  apply holeH_eq_zero
  intro i hi
  have hi' : (i : ℝ) + 1 ≤ g := by exact_mod_cast Nat.succ_le_of_lt hi
  have h := abs_sub_abs_le_abs_sub x (3 * ((i : ℝ) + 1))
  rw [abs_of_pos (by positivity : (0 : ℝ) < 3 * ((i : ℝ) + 1))] at h
  linarith

theorem holeH_lt_outerH {x : ℝ} (hx : |x| < modelRadius g) : holeH g x < outerH g x := by
  have hR := modelRadius_pos g
  by_cases h : ∃ i < g, |x - 3 * ((i : ℝ) + 1)| ≤ 1
  · obtain ⟨i, hi, hxi⟩ := h
    refine (holeH_le_one g x).trans_lt ?_
    unfold outerH
    rw [lt_sqrt zero_le_one]
    have hi' : (i : ℝ) + 1 ≤ g := by exact_mod_cast Nat.succ_le_of_lt hi
    rw [abs_le] at hxi
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hx0 : 0 ≤ x := by linarith [hxi.1]
    have hx1 : x ≤ 3 * g + 1 := by linarith [hxi.2]
    have hx2 : x ^ 2 ≤ (3 * g + 1) ^ 2 := pow_le_pow_left₀ hx0 hx1 2
    rw [modelRadius_eq]
    nlinarith [Nat.cast_nonneg (α := ℝ) g]
  · push_neg at h
    rw [holeH_eq_zero g fun i hi => (h i hi).le]
    unfold outerH
    rw [sqrt_pos]
    have := abs_lt.mp hx
    nlinarith

theorem holeH_of_abs_eq {x : ℝ} (hx : |x| = modelRadius g) : holeH g x = 0 :=
  holeH_of_abs_ge g (by rw [hx, modelRadius_eq]; linarith)

theorem outerH_of_abs_eq {x : ℝ} (hx : |x| = modelRadius g) : outerH g x = 0 := by
  unfold outerH
  rw [← sq_abs x, hx, sub_self, sqrt_zero]

theorem holeH_le_outerH {x : ℝ} (hx : |x| ≤ modelRadius g) : holeH g x ≤ outerH g x := by
  rcases hx.lt_or_eq with hlt | heq
  · exact (holeH_lt_outerH g hlt).le
  · rw [holeH_of_abs_eq g heq]
    exact outerH_nonneg g x

/-! ### The upper face map -/

/-- `√(1 − u²)`. -/
def halfW (u : ℝ) : ℝ := √(1 - u ^ 2)

theorem continuous_halfW : Continuous halfW :=
  continuous_sqrt.comp (continuous_const.sub (continuous_pow 2))

theorem sq_lt_one_of_halfW_pos {u : ℝ} (hw : 0 < halfW u) : u ^ 2 < 1 := by
  unfold halfW at hw
  rw [sqrt_pos] at hw
  linarith

theorem pole_of_halfW_eq_zero {u : ℝ} (hu : u ∈ Set.Icc (-1 : ℝ) 1) (h : halfW u = 0) :
    u = -1 ∨ u = 1 := by
  have h1 : 1 - u ^ 2 ≤ 0 := sqrt_eq_zero'.mp h
  have h2 : (u + 1) * (u - 1) = 0 := by nlinarith [hu.1, hu.2]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · left
    linarith
  · right
    linarith

theorem abs_horiz_le (u : ℝ) : |horiz g u| ≤ modelRadius g := abs_le.mpr (horiz_mem g u)

theorem abs_horiz_lt {u : ℝ} (hu : u ^ 2 < 1) : |horiz g u| < modelRadius g := by
  have h := abs_lt.mp ((sq_lt_one_iff_abs_lt_one u).mp hu)
  rw [abs_lt]
  constructor
  · rw [← horiz_neg_one]
    exact strictMonoOn_horiz g ⟨le_rfl, by norm_num⟩ ⟨h.1.le, h.2.le⟩ h.1
  · rw [← horiz_one]
    exact strictMonoOn_horiz g ⟨h.1.le, h.2.le⟩ ⟨by norm_num, le_rfl⟩ h.2

theorem horiz_pole {u : ℝ} (hu : u = -1 ∨ u = 1) : |horiz g u| = modelRadius g := by
  rcases hu with rfl | rfl
  · rw [horiz_neg_one, abs_neg, abs_of_pos (modelRadius_pos g)]
  · rw [horiz_one, abs_of_pos (modelRadius_pos g)]

/-- The vertical fraction `(v + w)/(2w)`. -/
def vfrac (z : ℂ) : ℝ := (z.im + halfW z.re) / (2 * halfW z.re)

/-- The vertical coordinate of the upper face map. -/
def faceY (z : ℂ) : ℝ :=
  holeH g (horiz g z.re) + vfrac z * (outerH g (horiz g z.re) - holeH g (horiz g z.re))

/-- The upper face map. -/
def facePt (z : ℂ) : ModelBase := ![horiz g z.re, faceY g z]

theorem facePt_zero (z : ℂ) : facePt g z 0 = horiz g z.re := rfl

theorem facePt_one (z : ℂ) : facePt g z 1 = faceY g z := rfl

theorem re_mem_Icc {z : ℂ} (hz : ‖z‖ ≤ 1) : z.re ∈ Set.Icc (-1 : ℝ) 1 :=
  abs_le.mp ((Complex.abs_re_le_norm z).trans hz)

theorem im_sq_le {z : ℂ} (hz : ‖z‖ ≤ 1) : z.im ^ 2 ≤ 1 - z.re ^ 2 := by
  have h := Complex.sq_norm_sub_sq_re z
  have : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
  linarith

theorem abs_im_le_halfW {z : ℂ} (hz : ‖z‖ ≤ 1) : |z.im| ≤ halfW z.re :=
  abs_le_sqrt (im_sq_le hz)

theorem norm_le_one_of_sq {z : ℂ} (h : z.re ^ 2 + z.im ^ 2 ≤ 1) : ‖z‖ ≤ 1 := by
  have := Complex.sq_norm_sub_sq_re z
  nlinarith [norm_nonneg z]

theorem vfrac_mem {z : ℂ} (hz : ‖z‖ ≤ 1) : 0 ≤ vfrac z ∧ vfrac z ≤ 1 := by
  have h := abs_le.mp (abs_im_le_halfW hz)
  unfold vfrac
  rcases (sqrt_nonneg (1 - z.re ^ 2)).eq_or_lt with h0 | hpos
  · have hw0 : halfW z.re = 0 := h0.symm
    rw [hw0, mul_zero, div_zero]
    exact ⟨le_rfl, zero_le_one⟩
  · have hw : 0 < halfW z.re := hpos
    constructor
    · exact div_nonneg (by linarith [h.1]) (by linarith)
    · rw [div_le_one (by linarith)]
      linarith [h.2]

theorem faceY_mem {z : ℂ} (hz : ‖z‖ ≤ 1) :
    holeH g (horiz g z.re) ≤ faceY g z ∧ faceY g z ≤ outerH g (horiz g z.re) := by
  obtain ⟨h0, h1⟩ := vfrac_mem hz
  have hle := holeH_le_outerH g (abs_horiz_le g z.re)
  unfold faceY
  constructor
  · nlinarith [mul_nonneg h0 (sub_nonneg.mpr hle)]
  · nlinarith [mul_le_mul_of_nonneg_right h1 (sub_nonneg.mpr hle)]

theorem facePt_mem {z : ℂ} (hz : ‖z‖ ≤ 1) :
    facePt g z ∈ modelPlanarRegion g ∧ 0 ≤ facePt g z 1 := by
  obtain ⟨hlo, hhi⟩ := faceY_mem g hz
  have hy : 0 ≤ faceY g z := (holeH_nonneg g _).trans hlo
  have hx2 : horiz g z.re ^ 2 ≤ modelRadius g ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_horiz_le g z.re) 2
  refine ⟨(modelPlanarRegion_iff_disk_holes g _).mpr ⟨?_, ?_⟩, hy⟩
  · rw [facePt_zero, facePt_one]
    exact (le_outerH_iff g hy hx2).mp hhi
  · intro i hi hi0
    rw [facePt_zero, facePt_one]
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hi' : i' < g := by
      simp only [mem_range] at hi
      omega
    have := (holeH_le_iff g hy).mp hlo i' hi'
    push_cast
    exact this

theorem continuous_horiz_re : Continuous fun z : ℂ => horiz g z.re :=
  (continuous_horiz g).comp Complex.continuous_re

theorem continuousAt_faceY {z : ℂ} (hw : 0 < halfW z.re) : ContinuousAt (faceY g) z := by
  have hx := continuous_horiz_re g
  have hhole : Continuous fun z : ℂ => holeH g (horiz g z.re) := (continuous_holeH g).comp hx
  have houter : Continuous fun z : ℂ => outerH g (horiz g z.re) := (continuous_outerH g).comp hx
  have hW : Continuous fun z : ℂ => halfW z.re := continuous_halfW.comp Complex.continuous_re
  unfold faceY vfrac
  exact hhole.continuousAt.add
    (((Complex.continuous_im.add hW).continuousAt.div (continuous_const.mul hW).continuousAt
      (mul_pos two_pos hw).ne').mul (houter.sub hhole).continuousAt)

theorem continuousOn_faceY : ContinuousOn (faceY g) (Metric.closedBall 0 1) := by
  intro z hz
  have hz' : ‖z‖ ≤ 1 := by simpa using hz
  by_cases hw : 0 < halfW z.re
  · exact (continuousAt_faceY g hw).continuousWithinAt
  · have hw0 : halfW z.re = 0 := le_antisymm (not_lt.mp hw) (sqrt_nonneg _)
    have habs := horiz_pole g (pole_of_halfW_eq_zero (re_mem_Icc hz') hw0)
    have hval : faceY g z = 0 := by
      unfold faceY vfrac
      rw [hw0, mul_zero, div_zero, zero_mul, add_zero, holeH_of_abs_eq g habs]
    have hlim : Filter.Tendsto (fun w : ℂ => outerH g (horiz g w.re))
        (nhdsWithin z (Metric.closedBall 0 1)) (nhds 0) := by
      rw [← outerH_of_abs_eq g habs]
      exact ((continuous_outerH g).comp (continuous_horiz_re g)).continuousAt.continuousWithinAt
    show Filter.Tendsto (faceY g) (nhdsWithin z (Metric.closedBall 0 1)) (nhds (faceY g z))
    rw [hval]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with w hw'
      have : ‖w‖ ≤ 1 := by simpa using hw'
      exact (holeH_nonneg g _).trans (faceY_mem g this).1
    · filter_upwards [self_mem_nhdsWithin] with w hw'
      have : ‖w‖ ≤ 1 := by simpa using hw'
      exact (faceY_mem g this).2

theorem continuousOn_facePt : ContinuousOn (facePt g) (Metric.closedBall 0 1) := by
  refine continuousOn_pi.mpr fun i => ?_
  fin_cases i
  · exact (continuous_horiz_re g).continuousOn
  · exact continuousOn_faceY g

theorem facePt_injOn : Set.InjOn (facePt g) (Metric.closedBall 0 1) := by
  intro z hz z' hz' h
  have hz1 : ‖z‖ ≤ 1 := by simpa using hz
  have hz1' : ‖z'‖ ≤ 1 := by simpa using hz'
  have h0 : horiz g z.re = horiz g z'.re := by
    have := congrFun h 0
    rwa [facePt_zero, facePt_zero] at this
  have h1 : faceY g z = faceY g z' := by
    have := congrFun h 1
    rwa [facePt_one, facePt_one] at this
  have hre : z.re = z'.re := (strictMonoOn_horiz g).injOn (re_mem_Icc hz1) (re_mem_Icc hz1') h0
  refine Complex.ext hre ?_
  by_cases hw : 0 < halfW z.re
  · have hD := holeH_lt_outerH g (abs_horiz_lt g (sq_lt_one_of_halfW_pos hw))
    unfold faceY vfrac at h1
    rw [← hre] at h1
    have h2 := mul_right_cancel₀ (sub_ne_zero.mpr hD.ne') (add_left_cancel h1)
    rw [div_left_inj' (mul_pos two_pos hw).ne'] at h2
    linarith
  · have hw0 : halfW z.re = 0 := le_antisymm (not_lt.mp hw) (sqrt_nonneg _)
    have h3 := abs_im_le_halfW hz1
    rw [hw0] at h3
    have h4 := abs_im_le_halfW hz1'
    rw [← hre, hw0] at h4
    rw [abs_nonpos_iff.mp h3, abs_nonpos_iff.mp h4]

theorem exists_facePt {q : ModelBase} (hq : q ∈ modelPlanarRegion g) (hq1 : 0 ≤ q 1) :
    ∃ z : ℂ, ‖z‖ ≤ 1 ∧ facePt g z = q := by
  obtain ⟨hdisk, hholes⟩ := (modelPlanarRegion_iff_disk_holes g q).mp hq
  have hR := modelRadius_pos g
  have hx2 : q 0 ^ 2 ≤ modelRadius g ^ 2 := by nlinarith [sq_nonneg (q 1)]
  have hxabs : |q 0| ≤ modelRadius g := (sq_le_sq.mp hx2).trans_eq (abs_of_pos hR)
  have hxI : q 0 ∈ Set.Icc (horiz g (-1)) (horiz g 1) := by
    rw [horiz_neg_one, horiz_one]
    exact abs_le.mp hxabs
  obtain ⟨u, hu, hxu⟩ := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1)
    (continuous_horiz g).continuousOn hxI
  have hlo : holeH g (q 0) ≤ q 1 := (holeH_le_iff g hq1).mpr fun i hi => by
    have := hholes (i + 1) (by simp only [mem_range]; omega) (by omega)
    push_cast at this
    exact this
  have hhi : q 1 ≤ outerH g (q 0) := (le_outerH_iff g hq1 hx2).mpr hdisk
  have hq_eq : ∀ z : ℂ, z.re = u → faceY g z = q 1 → facePt g z = q := by
    intro z hzu hzy
    funext i
    fin_cases i
    · show horiz g z.re = q 0
      rw [hzu, hxu]
    · exact hzy
  by_cases hw : 0 < halfW u
  · have hu2 : u ^ 2 < 1 := sq_lt_one_of_halfW_pos hw
    have hD : holeH g (q 0) < outerH g (q 0) := by
      rw [← hxu]
      exact holeH_lt_outerH g (abs_horiz_lt g hu2)
    have hDne : outerH g (q 0) - holeH g (q 0) ≠ 0 := (sub_pos.mpr hD).ne'
    obtain ⟨lam, hlam⟩ : ∃ lam : ℝ,
        lam = (q 1 - holeH g (q 0)) / (outerH g (q 0) - holeH g (q 0)) := ⟨_, rfl⟩
    have hlam0 : 0 ≤ lam := by
      rw [hlam]
      exact div_nonneg (by linarith) (sub_pos.mpr hD).le
    have hlam1 : lam ≤ 1 := by
      rw [hlam, div_le_one (sub_pos.mpr hD)]
      linarith
    refine ⟨⟨u, (2 * lam - 1) * halfW u⟩, ?_, hq_eq _ rfl ?_⟩
    · apply norm_le_one_of_sq
      show u ^ 2 + ((2 * lam - 1) * halfW u) ^ 2 ≤ 1
      have hW2 : halfW u ^ 2 = 1 - u ^ 2 := sq_sqrt (by linarith)
      have h21 : (2 * lam - 1) ^ 2 ≤ 1 := by
        nlinarith [mul_nonneg hlam0 (sub_nonneg.mpr hlam1)]
      have := mul_le_mul_of_nonneg_right h21 (sq_nonneg (halfW u))
      nlinarith
    · show holeH g (horiz g u) + ((2 * lam - 1) * halfW u + halfW u) / (2 * halfW u) *
        (outerH g (horiz g u) - holeH g (horiz g u)) = q 1
      rw [hxu, show (2 * lam - 1) * halfW u + halfW u = lam * (2 * halfW u) by ring,
        mul_div_assoc, div_self (mul_pos two_pos hw).ne', mul_one, hlam,
        div_mul_cancel₀ _ hDne]
      ring
  · have hw0 : halfW u = 0 := le_antisymm (not_lt.mp hw) (sqrt_nonneg _)
    have hpole := pole_of_halfW_eq_zero hu hw0
    have habs : |q 0| = modelRadius g := by
      rw [← hxu]
      exact horiz_pole g hpole
    have hq10 : q 1 = 0 := by
      have h := sq_abs (q 0)
      rw [habs] at h
      have : q 1 ^ 2 ≤ 0 := by nlinarith
      nlinarith [sq_nonneg (q 1)]
    refine ⟨⟨u, 0⟩, ?_, hq_eq _ rfl ?_⟩
    · apply norm_le_one_of_sq
      show u ^ 2 + 0 ^ 2 ≤ 1
      rcases hpole with rfl | rfl <;> norm_num
    · show holeH g (horiz g u) + (0 + halfW u) / (2 * halfW u) *
        (outerH g (horiz g u) - holeH g (horiz g u)) = q 1
      rw [hw0, mul_zero, div_zero, zero_mul, add_zero, hxu, holeH_of_abs_eq g habs, hq10]

/-! ### The circles of the planar model -/

theorem modelFactor_eval (i : ℕ) (q : ModelBase) :
    modelFactor g i (modelHeightPoint q 0) =
      (q 0 - 3 * i) ^ 2 + q 1 ^ 2 - (if i = 0 then modelRadius g else 1) ^ 2 := by
  simp [modelFactor, modelCircleFactor, modelHeightPoint]

theorem product_zero_iff (q : ModelBase) :
    modelPlanarProduct g q = 0 ↔ q 0 ^ 2 + q 1 ^ 2 = modelRadius g ^ 2 ∨
      ∃ i < g, (q 0 - 3 * ((i : ℝ) + 1)) ^ 2 + q 1 ^ 2 = 1 := by
  rw [modelPlanarProduct_zero_iff_circles]
  constructor
  · rintro ⟨i, hi, h⟩
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · left
      rw [modelFactor_eval, if_pos rfl] at h
      norm_num at h
      linarith
    · right
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      refine ⟨i', by simp only [mem_range] at hi; omega, ?_⟩
      rw [modelFactor_eval, if_neg (Nat.add_one_ne_zero i')] at h
      push_cast at h
      linarith
  · rintro (h | ⟨i, hi, h⟩)
    · refine ⟨0, by simp, ?_⟩
      rw [modelFactor_eval, if_pos rfl]
      norm_num
      linarith
    · refine ⟨i + 1, by simp only [mem_range]; omega, ?_⟩
      rw [modelFactor_eval, if_neg (Nat.add_one_ne_zero i)]
      push_cast
      linarith

/-! ### Points of the boundary circle -/

/-- The boundary point with angle `π(j + t)/(2g+1)`: parameter `t` on side `j` of the
`(4g+2)`-gon. -/
def sidePt (j : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (((π * ((j : ℝ) + t) / (2 * g + 1) : ℝ) : ℂ) * Complex.I)

theorem sidePt_re (j : ℕ) (t : ℝ) :
    (sidePt g j t).re = cos (π * ((j : ℝ) + t) / (2 * g + 1)) :=
  Complex.exp_ofReal_mul_I_re _

theorem sidePt_im (j : ℕ) (t : ℝ) :
    (sidePt g j t).im = sin (π * ((j : ℝ) + t) / (2 * g + 1)) :=
  Complex.exp_ofReal_mul_I_im _

theorem norm_sidePt (j : ℕ) (t : ℝ) : ‖sidePt g j t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem sidePt_shift (j m : ℕ) (t : ℝ) : sidePt g (j + m) t = sidePt g j (m + t) := by
  unfold sidePt
  rw [show ((j + m : ℕ) : ℝ) + t = (j : ℝ) + (m + t) by push_cast; ring]

theorem sidePt_eq_shift (j : ℕ) (t : ℝ) : sidePt g j t = sidePt g 0 (j + t) := by
  unfold sidePt
  rw [Nat.cast_zero, zero_add]

theorem side_angle_nonneg (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ π * ((j : ℝ) + t) / (2 * g + 1) := by
  positivity

theorem side_angle_le_pi {j : ℕ} (hj : j ≤ 2 * g) {t : ℝ} (ht : t ≤ 1) :
    π * ((j : ℝ) + t) / (2 * g + 1) ≤ π := by
  have hj' : (j : ℝ) ≤ 2 * g := by exact_mod_cast hj
  rw [div_le_iff₀ (by positivity)]
  have := mul_le_mul_of_nonneg_left (show (j : ℝ) + t ≤ 2 * g + 1 by linarith) pi_pos.le
  linarith

theorem side_angle_lower (k : ℕ) (t : ℝ) :
    π * (((2 * g + 1 + k : ℕ) : ℝ) + t) / (2 * g + 1) = π * ((k : ℝ) + t) / (2 * g + 1) + π := by
  have h : (2 * (g : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem angleParam_upper {j : ℕ} (hj : j ≤ 2 * g) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    angleParam g (sidePt g j t).re = 2 * g + 1 - (j + t) := by
  have h : (2 * (g : ℝ) + 1) ≠ 0 := by positivity
  rw [sidePt_re, angleParam, ← cos_pi_sub, arccos_cos (by linarith [side_angle_le_pi g hj ht₁])
    (by linarith [side_angle_nonneg g j ht₀])]
  first | (field_simp; ring) | field_simp

theorem angleParam_lower {k : ℕ} (hk : k ≤ 2 * g) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    angleParam g (sidePt g (2 * g + 1 + k) t).re = k + t := by
  have h : (2 * (g : ℝ) + 1) ≠ 0 := by positivity
  rw [sidePt_re, angleParam, side_angle_lower, cos_add_pi, neg_neg,
    arccos_cos (side_angle_nonneg g k ht₀) (side_angle_le_pi g hk ht₁)]
  first | (field_simp; ring) | field_simp

theorem horiz_lower {k : ℕ} (hk : k ≤ 2 * g) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    horiz g (sidePt g (2 * g + 1 + k) t).re = node g k + t * (node g (k + 1) - node g k) := by
  rw [horiz, angleParam_lower g hk ht₀ ht₁, tau_piece g hk ht₀ ht₁]

theorem sidePt_im_nonneg {j : ℕ} (hj : j ≤ 2 * g) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    0 ≤ (sidePt g j t).im := by
  rw [sidePt_im]
  exact sin_nonneg_of_nonneg_of_le_pi (side_angle_nonneg g j ht₀) (side_angle_le_pi g hj ht₁)

theorem sidePt_im_nonpos {k : ℕ} (hk : k ≤ 2 * g) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    (sidePt g (2 * g + 1 + k) t).im ≤ 0 := by
  rw [sidePt_im, side_angle_lower, sin_add_pi, neg_nonpos]
  exact sin_nonneg_of_nonneg_of_le_pi (side_angle_nonneg g k ht₀) (side_angle_le_pi g hk ht₁)

theorem sidePt_lower_arc {u : ℝ} (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    sidePt g (2 * g + 1) (angleParam g u) = ⟨u, -halfW u⟩ := by
  have h : (2 * (g : ℝ) + 1) ≠ 0 := by positivity
  have hθ : π * (((2 * g + 1 : ℕ) : ℝ) + angleParam g u) / (2 * g + 1) = arccos (-u) + π := by
    unfold angleParam
    push_cast
    first | (field_simp; ring) | field_simp
  apply Complex.ext
  · rw [sidePt_re, hθ, cos_add_pi, cos_arccos (by linarith [hu.2]) (by linarith [hu.1])]
    simp
  · rw [sidePt_im, hθ, sin_add_pi, sin_arccos]
    simp [halfW]

theorem sidePt_upper_arc {u : ℝ} (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    sidePt g 0 (2 * g + 1 - angleParam g u) = ⟨u, halfW u⟩ := by
  have h : (2 * (g : ℝ) + 1) ≠ 0 := by positivity
  have hθ : π * (((0 : ℕ) : ℝ) + (2 * g + 1 - angleParam g u)) / (2 * g + 1) =
      π - arccos (-u) := by
    unfold angleParam
    push_cast
    first | (field_simp; ring) | field_simp
  apply Complex.ext
  · rw [sidePt_re, hθ, cos_pi_sub, cos_arccos (by linarith [hu.2]) (by linarith [hu.1])]
    simp
  · rw [sidePt_im, hθ, sin_pi_sub, sin_arccos]
    simp [halfW]

theorem conj_sidePt {j : ℕ} (hj : j ≤ 4 * g + 1) (t : ℝ) :
    starRingEnd ℂ (sidePt g j t) = sidePt g (4 * g + 1 - j) (1 - t) := by
  have h : (2 * (g : ℝ) + 1) ≠ 0 := by positivity
  have hθ : π * (((4 * g + 1 - j : ℕ) : ℝ) + (1 - t)) / (2 * g + 1) =
      2 * π - π * ((j : ℝ) + t) / (2 * g + 1) := by
    rw [Nat.cast_sub hj]
    push_cast
    first | (field_simp; ring) | field_simp
  apply Complex.ext
  · rw [Complex.conj_re, sidePt_re, sidePt_re, hθ, cos_two_pi_sub]
  · rw [Complex.conj_im, sidePt_im, sidePt_im, hθ, sin_two_pi_sub]

/-! ### The upper face map on the boundary circle -/

theorem halfW_of_norm_eq {z : ℂ} (hz : ‖z‖ = 1) : halfW z.re = |z.im| := by
  have h := Complex.sq_norm_sub_sq_re z
  rw [hz, one_pow] at h
  unfold halfW
  rw [h, sqrt_sq_eq_abs]

theorem faceY_of_upper {z : ℂ} (hz : ‖z‖ = 1) (him : 0 ≤ z.im) :
    faceY g z = outerH g (horiz g z.re) := by
  have hw := halfW_of_norm_eq hz
  rw [abs_of_nonneg him] at hw
  rcases him.lt_or_eq with hpos | hzero
  · unfold faceY vfrac
    rw [hw, ← two_mul, div_self (mul_ne_zero two_ne_zero hpos.ne'), one_mul]
    ring
  · have hre : z.re = -1 ∨ z.re = 1 :=
      pole_of_halfW_eq_zero (re_mem_Icc hz.le) (by rw [hw, ← hzero])
    have habs := horiz_pole g hre
    unfold faceY vfrac
    rw [hw, ← hzero, add_zero, mul_zero, div_zero, zero_mul, add_zero, holeH_of_abs_eq g habs,
      outerH_of_abs_eq g habs]

theorem faceY_of_lower {z : ℂ} (hz : ‖z‖ = 1) (him : z.im ≤ 0) :
    faceY g z = holeH g (horiz g z.re) := by
  have hw := halfW_of_norm_eq hz
  rw [abs_of_nonpos him] at hw
  unfold faceY vfrac
  rw [hw, show z.im + -z.im = 0 by ring, zero_div, zero_mul, add_zero]

/-- The upper sides map to the outer circle. -/
theorem product_upper_side {j : ℕ} (hj : j ≤ 2 * g) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    modelPlanarProduct g (facePt g (sidePt g j t)) = 0 := by
  rw [product_zero_iff]
  left
  rw [facePt_zero, facePt_one,
    faceY_of_upper g (norm_sidePt g j t) (sidePt_im_nonneg g hj ht₀ ht₁)]
  have hx2 : horiz g (sidePt g j t).re ^ 2 ≤ modelRadius g ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_horiz_le g _) 2
  unfold outerH
  rw [sq_sqrt (by linarith)]
  ring

/-- The odd lower sides map to the hole circles. -/
theorem product_hole_side {i : ℕ} (hi : i < g) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    modelPlanarProduct g (facePt g (sidePt g (2 * g + 1 + (2 * i + 1)) t)) = 0 := by
  rw [product_zero_iff]
  right
  refine ⟨i, hi, ?_⟩
  have hk : 2 * i + 1 ≤ 2 * g := by omega
  rw [facePt_zero, facePt_one,
    faceY_of_lower g (norm_sidePt g _ t) (sidePt_im_nonpos g hk ht₀ ht₁), horiz_lower g hk ht₀ ht₁,
    show 2 * i + 1 + 1 = 2 * i + 2 by ring, node_left g hi, node_right g hi]
  set x := 3 * ((i : ℝ) + 1) - 1 + t * (3 * ((i : ℝ) + 1) + 1 - (3 * ((i : ℝ) + 1) - 1)) with hx
  have hxc : x - 3 * ((i : ℝ) + 1) = 2 * t - 1 := by rw [hx]; ring
  have habs : |x - 3 * ((i : ℝ) + 1)| ≤ 1 := by
    rw [hxc, abs_le]
    constructor <;> linarith
  have hsq : 0 ≤ 1 - (x - 3 * ((i : ℝ) + 1)) ^ 2 := by
    rw [hxc]
    nlinarith [mul_nonneg ht₀ (sub_nonneg.mpr ht₁)]
  rw [holeH_eq_term g hi habs, sq_sqrt hsq]
  ring

theorem holeH_eq_zero_of_seg {j₀ : ℕ} (hj₀ : j₀ ≤ g) {x : ℝ} (h₁ : node g (2 * j₀) ≤ x)
    (h₂ : x ≤ node g (2 * j₀ + 1)) : holeH g x = 0 := by
  apply holeH_eq_zero
  intro i hi
  by_cases hij : i + 1 ≤ j₀
  · obtain ⟨j', rfl⟩ : ∃ j', j₀ = j' + 1 := ⟨j₀ - 1, by omega⟩
    rw [show 2 * (j' + 1) = 2 * j' + 2 by ring, node_right g (by omega)] at h₁
    have : (i : ℝ) + 1 ≤ j' + 1 := by exact_mod_cast hij
    exact le_trans (by linarith) (le_abs_self _)
  · have hj₀g : j₀ < g := by omega
    rw [node_left g hj₀g] at h₂
    have : (j₀ : ℝ) + 1 ≤ i + 1 := by exact_mod_cast (show j₀ + 1 ≤ i + 1 by omega)
    exact le_trans (by linarith) (neg_le_abs _)

/-- The even lower sides map to the `x`-axis. -/
theorem faceY_seg_side {j₀ : ℕ} (hj₀ : j₀ ≤ g) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    faceY g (sidePt g (2 * g + 1 + 2 * j₀) t) = 0 := by
  have hk : 2 * j₀ ≤ 2 * g := by omega
  rw [faceY_of_lower g (norm_sidePt g _ t) (sidePt_im_nonpos g hk ht₀ ht₁),
    horiz_lower g hk ht₀ ht₁]
  have hlt := node_lt_succ g hk
  apply holeH_eq_zero_of_seg g hj₀
  · nlinarith [mul_nonneg ht₀ (sub_nonneg.mpr hlt.le)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr ht₁) (sub_nonneg.mpr hlt.le)]

/-! ### Boundary points of the upper face map come from sides -/

theorem exists_nat_piece {b : ℝ} {N : ℕ} (hb₀ : 0 ≤ b) (hb₁ : b ≤ N + 1) :
    ∃ j : ℕ, j ≤ N ∧ (j : ℝ) ≤ b ∧ b ≤ j + 1 := by
  by_cases h : ⌊b⌋₊ ≤ N
  · exact ⟨⌊b⌋₊, h, Nat.floor_le hb₀, (Nat.lt_floor_add_one b).le⟩
  · refine ⟨N, le_rfl, ?_, hb₁⟩
    have : (N : ℝ) + 1 ≤ ⌊b⌋₊ := by exact_mod_cast (show N + 1 ≤ ⌊b⌋₊ by omega)
    linarith [Nat.floor_le hb₀]

/-- A point of the closed disk sent to the `x`-axis lies on an even lower side. -/
theorem exists_seg_side {z : ℂ} (hz : ‖z‖ ≤ 1) (hy : faceY g z = 0) :
    ∃ j₀ ≤ g, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = sidePt g (2 * g + 1 + 2 * j₀) t := by
  have hle := holeH_le_outerH g (abs_horiz_le g z.re)
  obtain ⟨hv0, hv1⟩ := vfrac_mem hz
  have hh0 := holeH_nonneg g (horiz g z.re)
  have hprod : 0 ≤ vfrac z * (outerH g (horiz g z.re) - holeH g (horiz g z.re)) :=
    mul_nonneg hv0 (sub_nonneg.mpr hle)
  have hy' := hy
  unfold faceY at hy'
  have hhole : holeH g (horiz g z.re) = 0 := by linarith
  have hvD : vfrac z * (outerH g (horiz g z.re) - holeH g (horiz g z.re)) = 0 := by linarith
  have him : z.im = -halfW z.re := by
    by_cases hw : 0 < halfW z.re
    · have hD := holeH_lt_outerH g (abs_horiz_lt g (sq_lt_one_of_halfW_pos hw))
      have hv : vfrac z = 0 := (mul_eq_zero.mp hvD).resolve_right (sub_pos.mpr hD).ne'
      unfold vfrac at hv
      rw [div_eq_zero_iff] at hv
      rcases hv with hv | hv <;> linarith
    · have hw0 : halfW z.re = 0 := le_antisymm (not_lt.mp hw) (sqrt_nonneg _)
      have h3 := abs_im_le_halfW hz
      rw [hw0] at h3
      rw [hw0, abs_nonpos_iff.mp h3, neg_zero]
  have ha₀ := angleParam_nonneg g z.re
  have ha₁ := angleParam_le g z.re
  have hzeq : z = sidePt g (2 * g + 1) (angleParam g z.re) := by
    rw [sidePt_lower_arc g (re_mem_Icc hz)]
    exact Complex.ext rfl him
  have hx : horiz g z.re = tau g (angleParam g z.re) := rfl
  rw [hx] at hhole
  set a := angleParam g z.re with ha
  obtain ⟨k, hk, hka, hak⟩ := exists_nat_piece (N := 2 * g) ha₀ (by push_cast; linarith)
  rcases Nat.even_or_odd' k with ⟨j₀, rfl | rfl⟩
  · push_cast at hka hak
    refine ⟨j₀, by omega, a - 2 * j₀, by linarith, by linarith, ?_⟩
    rw [hzeq, sidePt_shift g (2 * g + 1) (2 * j₀)]
    congr 1
    push_cast
    ring
  · have hj₀ : j₀ < g := by omega
    push_cast at hka hak
    rcases hka.eq_or_lt with h1 | h1
    · refine ⟨j₀, hj₀.le, 1, zero_le_one, le_rfl, ?_⟩
      rw [hzeq, sidePt_shift g (2 * g + 1) (2 * j₀), ← h1]
      congr 1
      push_cast
      ring
    rcases hak.eq_or_lt with h2 | h2
    · refine ⟨j₀ + 1, hj₀, 0, le_rfl, zero_le_one, ?_⟩
      rw [hzeq, sidePt_shift g (2 * g + 1) (2 * (j₀ + 1)), h2]
      congr 1
      push_cast
      ring
    · exfalso
      have hlo : node g (2 * j₀ + 1) < tau g a := by
        rw [← tau_nat g (m := 2 * j₀ + 1) (by omega)]
        exact tau_lt g (by positivity) (by push_cast; linarith) ha₁
      have hhi : tau g a < node g (2 * j₀ + 2) := by
        rw [← tau_nat g (m := 2 * j₀ + 2) (by omega)]
        exact tau_lt g ha₀ (by push_cast; linarith)
          (by exact_mod_cast (show 2 * j₀ + 2 ≤ 2 * g + 1 by omega))
      rw [node_left g hj₀] at hlo
      rw [node_right g hj₀] at hhi
      have habs : |tau g a - 3 * ((j₀ : ℝ) + 1)| < 1 := by
        rw [abs_lt]
        constructor <;> linarith
      rw [holeH_eq_term g hj₀ habs.le, sqrt_eq_zero'] at hhole
      have := abs_lt.mp habs
      nlinarith

/-- A point of the closed disk sent to a boundary circle lies on an upper side or an odd lower
side. -/
theorem exists_boundary_side {z : ℂ} (hz : ‖z‖ ≤ 1)
    (hb : modelPlanarProduct g (facePt g z) = 0) :
    ∃ j : ℕ, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = sidePt g j t ∧
      (j ≤ 2 * g ∨ ∃ i < g, j = 2 * g + 1 + (2 * i + 1)) := by
  have hle := holeH_le_outerH g (abs_horiz_le g z.re)
  obtain ⟨hlo, hhi⟩ := faceY_mem g hz
  have hy0 : 0 ≤ faceY g z := (holeH_nonneg g _).trans hlo
  have ha₀ := angleParam_nonneg g z.re
  have ha₁ := angleParam_le g z.re
  rw [product_zero_iff, facePt_zero, facePt_one] at hb
  rcases hb with hout | ⟨i, hi, hhole⟩
  · have hyo : faceY g z = outerH g (horiz g z.re) := by
      unfold outerH
      rw [eq_comm, sqrt_eq_iff_eq_sq (by nlinarith [sq_nonneg (faceY g z)]) hy0]
      linarith
    have him : z.im = halfW z.re := by
      by_cases hw : 0 < halfW z.re
      · have hD := holeH_lt_outerH g (abs_horiz_lt g (sq_lt_one_of_halfW_pos hw))
        unfold faceY at hyo
        have hv : vfrac z = 1 := by
          have h0 : (vfrac z - 1) * (outerH g (horiz g z.re) - holeH g (horiz g z.re)) = 0 := by
            linarith
          have := (mul_eq_zero.mp h0).resolve_right (sub_pos.mpr hD).ne'
          linarith
        unfold vfrac at hv
        rw [div_eq_one_iff_eq (mul_pos two_pos hw).ne'] at hv
        linarith
      · have hw0 : halfW z.re = 0 := le_antisymm (not_lt.mp hw) (sqrt_nonneg _)
        have h3 := abs_im_le_halfW hz
        rw [hw0] at h3
        rw [hw0, abs_nonpos_iff.mp h3]
    have hzeq : z = sidePt g 0 (2 * g + 1 - angleParam g z.re) := by
      rw [sidePt_upper_arc g (re_mem_Icc hz)]
      exact Complex.ext rfl him
    set a := angleParam g z.re with ha
    obtain ⟨j, hj, hjb, hbj⟩ := exists_nat_piece (N := 2 * g) (b := 2 * g + 1 - a)
      (by linarith) (by push_cast; linarith)
    refine ⟨j, 2 * g + 1 - a - j, by linarith, by linarith, ?_, Or.inl hj⟩
    rw [hzeq, sidePt_eq_shift g j]
    congr 1
    ring
  · have hsq : (horiz g z.re - 3 * ((i : ℝ) + 1)) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (faceY g z)]
    have habs : |horiz g z.re - 3 * ((i : ℝ) + 1)| ≤ 1 := (sq_le_one_iff_abs_le_one _).mp hsq
    have hyh : faceY g z = holeH g (horiz g z.re) := by
      rw [holeH_eq_term g hi habs, eq_comm, sqrt_eq_iff_eq_sq (by linarith) hy0]
      linarith
    have hw : 0 < halfW z.re := by
      by_contra hw
      have hw0 : halfW z.re = 0 := le_antisymm (not_lt.mp hw) (sqrt_nonneg _)
      have hpole := horiz_pole g (pole_of_halfW_eq_zero (re_mem_Icc hz) hw0)
      have hi' : (i : ℝ) + 1 ≤ g := by exact_mod_cast Nat.succ_le_of_lt hi
      rw [abs_le] at habs
      rw [modelRadius_eq] at hpole
      rcases (abs_eq (by positivity)).mp hpole with h | h <;> linarith [habs.1, habs.2]
    have hD := holeH_lt_outerH g (abs_horiz_lt g (sq_lt_one_of_halfW_pos hw))
    have him : z.im = -halfW z.re := by
      unfold faceY at hyh
      have hv : vfrac z = 0 := by
        have h0 : vfrac z * (outerH g (horiz g z.re) - holeH g (horiz g z.re)) = 0 := by
          linarith
        exact (mul_eq_zero.mp h0).resolve_right (sub_pos.mpr hD).ne'
      unfold vfrac at hv
      rw [div_eq_zero_iff] at hv
      rcases hv with hv | hv <;> linarith
    have hzeq : z = sidePt g (2 * g + 1) (angleParam g z.re) := by
      rw [sidePt_lower_arc g (re_mem_Icc hz)]
      exact Complex.ext rfl him
    have hx : horiz g z.re = tau g (angleParam g z.re) := rfl
    rw [hx] at habs
    set a := angleParam g z.re with ha
    have hi' : (2 * (i : ℝ) + 2) ≤ 2 * g + 1 := by
      have : (i : ℝ) + 1 ≤ g := by exact_mod_cast Nat.succ_le_of_lt hi
      linarith
    rw [abs_le] at habs
    have hlo' : 2 * (i : ℝ) + 1 ≤ a := by
      by_contra hlt
      push_neg at hlt
      have := tau_lt g ha₀ hlt (by linarith)
      rw [show 2 * (i : ℝ) + 1 = ((2 * i + 1 : ℕ) : ℝ) by push_cast; ring,
        tau_nat g (by omega), node_left g hi] at this
      linarith [habs.1]
    have hhi' : a ≤ 2 * (i : ℝ) + 2 := by
      by_contra hlt
      push_neg at hlt
      have := tau_lt g (by positivity) hlt ha₁
      rw [show 2 * (i : ℝ) + 2 = ((2 * i + 2 : ℕ) : ℝ) by push_cast; ring,
        tau_nat g (by omega), node_right g hi] at this
      linarith [habs.2]
    refine ⟨2 * g + 1 + (2 * i + 1), a - (2 * i + 1), by linarith, by linarith, ?_,
      Or.inr ⟨i, hi, rfl⟩⟩
    rw [hzeq, sidePt_shift g (2 * g + 1) (2 * i + 1)]
    congr 1
    push_cast
    ring

/-! ### The lower face map -/

/-- The reflection in the `x`-axis. -/
def reflect (q : ModelBase) : ModelBase := ![q 0, -q 1]

theorem reflect_zero (q : ModelBase) : reflect q 0 = q 0 := rfl

theorem reflect_one (q : ModelBase) : reflect q 1 = -q 1 := rfl

theorem reflect_reflect (q : ModelBase) : reflect (reflect q) = q := by
  funext i
  fin_cases i
  · rfl
  · show -(-q 1) = q 1
    ring

theorem reflect_of_one_eq_zero {q : ModelBase} (h : q 1 = 0) : reflect q = q := by
  funext i
  fin_cases i
  · rfl
  · show -q 1 = q 1
    rw [h, neg_zero]

theorem reflect_injective : Function.Injective reflect := fun q q' h => by
  rw [← reflect_reflect q, h, reflect_reflect]

theorem continuous_reflect : Continuous reflect := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_apply 0
  · exact (continuous_apply 1).neg

theorem reflect_mem {q : ModelBase} (hq : q ∈ modelPlanarRegion g) :
    reflect q ∈ modelPlanarRegion g := by
  rw [modelPlanarRegion_iff_disk_holes] at hq ⊢
  simp only [reflect_zero, reflect_one, neg_sq]
  exact hq

theorem product_reflect (q : ModelBase) :
    modelPlanarProduct g (reflect q) = modelPlanarProduct g q := by
  unfold modelPlanarProduct
  refine prod_congr rfl fun i _ => ?_
  rw [modelFactor_eval, modelFactor_eval, reflect_zero, reflect_one, neg_sq]

/-- The lower face map: the mirror image of the upper face map at the conjugate point. -/
def facePtLow (z : ℂ) : ModelBase := reflect (facePt g (starRingEnd ℂ z))

theorem mem_closedBall_conj {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    starRingEnd ℂ z ∈ Metric.closedBall (0 : ℂ) 1 := by
  simpa [Complex.norm_conj] using hz

theorem facePtLow_mem {z : ℂ} (hz : ‖z‖ ≤ 1) :
    facePtLow g z ∈ modelPlanarRegion g ∧ facePtLow g z 1 ≤ 0 := by
  have hz' : ‖starRingEnd ℂ z‖ ≤ 1 := by rwa [Complex.norm_conj]
  obtain ⟨hm, hy⟩ := facePt_mem g hz'
  exact ⟨reflect_mem g hm, by rw [facePtLow, reflect_one]; linarith⟩

theorem continuousOn_facePtLow : ContinuousOn (facePtLow g) (Metric.closedBall 0 1) :=
  continuous_reflect.comp_continuousOn
    ((continuousOn_facePt g).comp Complex.continuous_conj.continuousOn
      fun _ hz => mem_closedBall_conj hz)

theorem facePtLow_injOn : Set.InjOn (facePtLow g) (Metric.closedBall 0 1) := by
  intro z hz z' hz' h
  have := facePt_injOn g (mem_closedBall_conj hz) (mem_closedBall_conj hz') (reflect_injective h)
  simpa using congrArg (starRingEnd ℂ) this

theorem exists_facePtLow {q : ModelBase} (hq : q ∈ modelPlanarRegion g) (hq1 : q 1 ≤ 0) :
    ∃ z : ℂ, ‖z‖ ≤ 1 ∧ facePtLow g z = q := by
  obtain ⟨z, hz, hzq⟩ := exists_facePt g (reflect_mem g hq) (by rw [reflect_one]; linarith)
  refine ⟨starRingEnd ℂ z, by rwa [Complex.norm_conj], ?_⟩
  rw [facePtLow, Complex.conj_conj, hzq, reflect_reflect]

/-- If the two face maps agree, the point is on the `x`-axis and the two preimages are
conjugate. -/
theorem facePt_eq_facePtLow {z z' : ℂ} (hz : ‖z‖ ≤ 1) (hz' : ‖z'‖ ≤ 1)
    (h : facePt g z = facePtLow g z') : z' = starRingEnd ℂ z ∧ faceY g z = 0 := by
  have hz'c : ‖starRingEnd ℂ z'‖ ≤ 1 := by rwa [Complex.norm_conj]
  have h1 := congrFun h 1
  rw [facePt_one, facePtLow, reflect_one, facePt_one] at h1
  have hy := (facePt_mem g hz).2
  have hy' := (facePt_mem g hz'c).2
  rw [facePt_one] at hy hy'
  have hy0 : faceY g z = 0 := by linarith
  have hy0' : faceY g (starRingEnd ℂ z') = 0 := by linarith
  refine ⟨?_, hy0⟩
  have hfix : facePtLow g z' = facePt g (starRingEnd ℂ z') :=
    reflect_of_one_eq_zero (by rw [facePt_one]; exact hy0')
  rw [hfix] at h
  have := facePt_injOn g (by simpa using hz) (by simpa using hz'c) h
  rw [this, Complex.conj_conj]

end ModelFace
end R4Embedding
