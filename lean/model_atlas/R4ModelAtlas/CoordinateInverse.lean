import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
Adapted excerpt from DifferentialGeometry at
bafefb7ce5ce7e40417641d67e6e95727b7bba1f,
Topology/Morse/RegularLevel/LevelSet.lean (original lines 16–209 and 317–454).
Changes: separate namespace, explicit finite-coordinate model and imports;
unneeded implicit-function and Morse normal-form dependencies are omitted.
License: ../third_party/differential-geometry/LICENSE (Apache-2.0).
The fixed original sources remain unchanged.
-/

open scoped Topology
noncomputable section
namespace R4ModelAtlas
abbrev MorseModel (n : ℕ) : Type := Fin n → ℝ

abbrev LevelSetSpace {M : Type*} (f : M → ℝ) (a : ℝ) : Type _ := {x : M // f x = a}

noncomputable def levelSetReindex {m : ℕ} (e : Fin (m + 1) ≃ Fin (m + 1)) :
    MorseModel (m + 1) ≃ₗ[ℝ] MorseModel (m + 1) where
  toFun := fun v j => v (e.symm j)
  map_add' := by
    intro x y
    ext j
    rfl
  map_smul' := by
    intro a x
    ext j
    rfl
  invFun := fun v j => v (e j)
  left_inv := by
    intro v
    ext j
    simp
  right_inv := by
    intro v
    ext j
    simp

theorem levelSetReindex_apply {m : ℕ} (e : Fin (m + 1) ≃ Fin (m + 1))
    (v : MorseModel (m + 1)) (j : Fin (m + 1)) :
    levelSetReindex e v j = v (e.symm j) := rfl

theorem levelSetReindex_comp {m : ℕ} (e₁ e₂ : Fin (m + 1) ≃ Fin (m + 1))
    (v : MorseModel (m + 1)) :
    levelSetReindex e₁ (levelSetReindex e₂ v) = levelSetReindex (e₂.trans e₁) v := by
  ext j
  simp [levelSetReindex_apply]

theorem levelSetReindex_symm {m : ℕ} (e : Fin (m + 1) ≃ Fin (m + 1))
    (v : MorseModel (m + 1)) :
    levelSetReindex e (levelSetReindex e.symm v) = v := by
  ext j
  simp [levelSetReindex_apply]

theorem levelSetReindex_lastBasis {m : ℕ} (i : Fin (m + 1)) :
    levelSetReindex (Equiv.swap i (Fin.last m))
        (fun j : Fin (m + 1) => if j = Fin.last m then (1 : ℝ) else 0) =
      (fun j : Fin (m + 1) => if j = i then (1 : ℝ) else 0) := by
  ext j
  rw [levelSetReindex_apply]
  by_cases hj : j = i
  · subst j
    have h : (Equiv.swap i (Fin.last m)).symm i = Fin.last m := by simp
    rw [h]
    simp
  · have hne : (Equiv.swap i (Fin.last m)).symm j ≠ Fin.last m := by
      intro h'
      apply hj
      have hback := congrArg (Equiv.swap i (Fin.last m)) h'
      simpa using hback
    rw [ite_eq_right hne]
    simp [hj]

theorem exists_coord_of_fderiv_ne_zero {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (y : MorseModel (m + 1)) (h : fderiv ℝ g y ≠ 0) :
    ∃ i : Fin (m + 1), (fderiv ℝ g y)
      (fun j : Fin (m + 1) => if j = i then (1 : ℝ) else 0) ≠ 0 := by
  by_contra hz
  apply h
  apply ContinuousLinearMap.ext
  intro v
  have hv : v = ∑ j : Fin (m + 1), v j • (fun k : Fin (m + 1) => if k = j then (1 : ℝ) else 0) := by
    ext k
    simp [Finset.sum_apply, Pi.smul_apply]
  have hzall : ∀ j : Fin (m + 1), (fderiv ℝ g y)
      (fun k : Fin (m + 1) => if k = j then (1 : ℝ) else 0) = 0 := by
    intro j
    by_contra hne
    exact hz ⟨j, hne⟩
  rw [hv]
  simp [hzall]

noncomputable def levelSetSplit (m : ℕ) : (MorseModel m × ℝ) ≃ₗ[ℝ] MorseModel (m + 1) where
  toFun := fun p j =>
    if h : j = Fin.last m then p.2 else p.1 (Fin.castPred j h)
  map_add' := by
    intro x y
    ext j
    by_cases h : j = Fin.last m <;> simp [h]
  map_smul' := by
    intro a x
    ext j
    by_cases h : j = Fin.last m <;> simp [h]
  invFun := fun v => ((fun i : Fin m => v (Fin.castSucc i)), v (Fin.last m))
  left_inv := by
    intro p
    ext i
    · change (fun j : Fin (m + 1) => if h : j = Fin.last m then p.2 else p.1 (Fin.castPred j h))
          (Fin.castSucc i) = p.1 i
      have h : Fin.castSucc i ≠ Fin.last m := Fin.castSucc_ne_last i
      simp [h]
    · change (fun j : Fin (m + 1) => if h : j = Fin.last m then p.2 else p.1 (Fin.castPred j h))
          (Fin.last m) = p.2
      simp
  right_inv := by
    intro v
    ext j
    by_cases h : j = Fin.last m
    · subst j
      simp
    · change (if h : Fin.castSucc (Fin.castPred j h) = Fin.last m then v (Fin.last m)
          else v (Fin.castSucc (Fin.castPred j h))) = v j
      have hne : Fin.castSucc (Fin.castPred j h) ≠ Fin.last m := Fin.castSucc_ne_last (Fin.castPred j h)
      rw [dite_eq_right hne]
      rw [Fin.castSucc_castPred j h]

noncomputable def scalarLinearEquiv {𝕜 : Type*} [NormedField 𝕜] (c : 𝕜) (hc : c ≠ 0) :
    𝕜 ≃L[𝕜] 𝕜 where
  toFun := fun z => c • z
  invFun := fun z => c⁻¹ • z
  map_add' := by
    intro x y
    simp [smul_eq_mul, mul_add]
  map_smul' := by
    intro a x
    simp [smul_eq_mul]
    ring
  continuous_toFun := continuous_id.const_smul c
  continuous_invFun := continuous_id.const_smul c⁻¹
  left_inv := by
    intro x
    change c⁻¹ • (c • x) = x
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  right_inv := by
    intro x
    change c • (c⁻¹ • x) = x
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

def levelSetLastBasis {m : ℕ} : MorseModel (m + 1) :=
  fun j : Fin (m + 1) => if j = Fin.last m then (1 : ℝ) else 0

theorem levelSetSplit_basis (m : ℕ) :
    levelSetSplit m (0, (1 : ℝ)) = levelSetLastBasis := by
  ext j
  by_cases hj : j = Fin.last m
  · subst j
    dsimp [levelSetSplit]
    simp [levelSetLastBasis]
  · dsimp [levelSetSplit]
    simp [hj, levelSetLastBasis]

theorem levelSetReindex_swap_swap {m : ℕ} (i : Fin (m + 1)) (u₀ : MorseModel (m + 1)) :
    levelSetReindex (Equiv.swap i (Fin.last m)) (levelSetReindex (Equiv.swap i (Fin.last m)) u₀) =
      u₀ := by
  have hs : (Equiv.swap i (Fin.last m)).symm = Equiv.swap i (Fin.last m) := by
    ext j
    simp
  rw [← hs]
  exact levelSetReindex_symm (Equiv.swap i (Fin.last m)) u₀

theorem levelSetReindex_lastDeriv_ne_zero {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (u₀ : MorseModel (m + 1)) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g u₀) (i : Fin (m + 1))
    (hi : (fderiv ℝ g u₀) (fun j : Fin (m + 1) => if j = i then (1 : ℝ) else 0) ≠ 0) :
    (fderiv ℝ (fun w => g (levelSetReindex (Equiv.swap i (Fin.last m)) w))
      (levelSetReindex (Equiv.swap i (Fin.last m)) u₀)) levelSetLastBasis ≠ 0 := by
  let e : Fin (m + 1) ≃ Fin (m + 1) := Equiv.swap i (Fin.last m)
  let u₁ : MorseModel (m + 1) := levelSetReindex e u₀
  have hder : fderiv ℝ (fun w => g (levelSetReindex e w)) u₁ =
      (fderiv ℝ g (levelSetReindex e u₁)).comp ((levelSetReindex e).toContinuousLinearEquiv :
        MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)) := by
    have hgdiff : DifferentiableAt ℝ g (levelSetReindex e u₁) := by
      rw [levelSetReindex_swap_swap]
      exact hg.differentiableAt (by norm_num)
    have hldiff : DifferentiableAt ℝ (fun w : MorseModel (m + 1) => levelSetReindex e w) u₁ :=
      ((levelSetReindex e).toContinuousLinearEquiv :
        MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).differentiableAt
    have hcomp := fderiv_comp u₁ (g := g) (f := fun w : MorseModel (m + 1) => levelSetReindex e w)
      hgdiff hldiff
    have hldiff_der : fderiv ℝ (fun w : MorseModel (m + 1) => levelSetReindex e w) u₁ =
        ((levelSetReindex e).toContinuousLinearEquiv :
          MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)) := by
      exact (ContinuousLinearMap.fderiv ((levelSetReindex e).toContinuousLinearEquiv :
        MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)))
    change fderiv ℝ (g ∘ fun w : MorseModel (m + 1) => levelSetReindex e w) u₁ = _
    simpa only [hldiff_der] using hcomp
  have hval : (fderiv ℝ g (levelSetReindex e u₁))
      (levelSetReindex e levelSetLastBasis) =
      (fderiv ℝ g u₀) (fun j : Fin (m + 1) => if j = i then (1 : ℝ) else 0) := by
    rw [levelSetReindex_swap_swap]
    have hlb : levelSetReindex e levelSetLastBasis =
        (fun j : Fin (m + 1) => if j = i then (1 : ℝ) else 0) := by
      change levelSetReindex e
        (fun j : Fin (m + 1) => if j = Fin.last m then (1 : ℝ) else 0) = _
      simpa only [e] using levelSetReindex_lastBasis i
    rw [hlb]
  rw [hder]
  change (fderiv ℝ g (levelSetReindex e u₁)) (levelSetReindex e levelSetLastBasis) ≠ 0
  rwa [hval]

def levelSetSplitFst (m : ℕ) : MorseModel (m + 1) →L[ℝ] MorseModel m :=
  (ContinuousLinearMap.fst ℝ (MorseModel m) ℝ).comp
    ((levelSetSplit m).symm.toContinuousLinearEquiv : MorseModel (m + 1) →L[ℝ] (MorseModel m × ℝ))

theorem levelSetSplitFst_split (m : ℕ) (y : MorseModel m) (z : ℝ) :
    levelSetSplitFst m (levelSetSplit m (y, z)) = y := by
  simp [levelSetSplitFst]

theorem levelSetSplit_add_basis (m : ℕ) (y : MorseModel m) (z : ℝ) :
    levelSetSplit m (y, z) = levelSetSplit m (y, 0) + z • levelSetLastBasis := by
  have hlin := (levelSetSplit m).map_add (y, (0 : ℝ)) (0, z)
  have hz : (levelSetSplit m) (0, z) = z • levelSetLastBasis := by
    rw [← levelSetSplit_basis m]
    simpa using (levelSetSplit m).map_smul z (0, (1 : ℝ))
  rw [hz] at hlin
  simpa [add_comm, add_left_comm, add_assoc] using hlin

noncomputable def levelSetChartDerivInvFun {m : ℕ} (D : MorseModel (m + 1) →L[ℝ] ℝ) :
    (ℝ × MorseModel m) → MorseModel (m + 1) :=
  fun q => levelSetSplit m (q.2, (q.1 - D (levelSetSplit m (q.2, 0))) / D levelSetLastBasis)

noncomputable def levelSetChartDerivEquiv {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (e : Fin (m + 1) ≃ Fin (m + 1)) (w : MorseModel (m + 1))
    (hc : (fderiv ℝ (fun v => g (levelSetReindex e v)) w) levelSetLastBasis ≠ 0) :
    MorseModel (m + 1) ≃L[ℝ] (ℝ × MorseModel m) where
  toFun := fun v => ((fderiv ℝ (fun v => g (levelSetReindex e v)) w) v, levelSetSplitFst m v)
  invFun := levelSetChartDerivInvFun (fderiv ℝ (fun v => g (levelSetReindex e v)) w)
  left_inv := by
    intro v
    let D : MorseModel (m + 1) →L[ℝ] ℝ := fderiv ℝ (fun v => g (levelSetReindex e v)) w
    let y : MorseModel m := levelSetSplitFst m v
    let z : ℝ := ((levelSetSplit m).symm v).2
    have hv : v = levelSetSplit m (y, z) := by
      have hsymm : (levelSetSplit m).symm v = (y, z) := by
        simp [y, z, levelSetSplitFst]
      rw [← hsymm]
      exact ((levelSetSplit m).apply_symm_apply v).symm
    have hlin : D (levelSetSplit m (y, z)) = D (levelSetSplit m (y, 0)) + z • D levelSetLastBasis := by
      rw [levelSetSplit_add_basis]
      rw [map_add, map_smul]
    change levelSetSplit m (y, (D v - D (levelSetSplit m (y, 0))) / D levelSetLastBasis) = v
    rw [hv]
    rw [hlin]
    have hz : (D (levelSetSplit m (y, 0)) + z • D levelSetLastBasis -
        D (levelSetSplit m (y, 0))) / D levelSetLastBasis = z := by
      rw [smul_eq_mul]
      rw [add_sub_cancel_left]
      rw [div_eq_mul_inv]
      rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]
    rw [hz]
  right_inv := by
    intro q
    let D : MorseModel (m + 1) →L[ℝ] ℝ := fderiv ℝ (fun v => g (levelSetReindex e v)) w
    change (D (levelSetSplit m (q.2, (q.1 - D (levelSetSplit m (q.2, 0))) / D levelSetLastBasis)),
        levelSetSplitFst m (levelSetSplit m (q.2, (q.1 - D (levelSetSplit m (q.2, 0))) / D levelSetLastBasis))) = q
    rw [levelSetSplitFst_split]
    apply Prod.ext
    · change D (levelSetSplit m (q.2, (q.1 - D (levelSetSplit m (q.2, 0))) / D levelSetLastBasis)) = q.1
      rw [levelSetSplit_add_basis]
      rw [map_add, map_smul]
      have hz : ((q.1 - D (levelSetSplit m (q.2, 0))) / D levelSetLastBasis) • D levelSetLastBasis =
          q.1 - D (levelSetSplit m (q.2, 0)) := by
        rw [smul_eq_mul]
        exact div_mul_cancel₀ (q.1 - D (levelSetSplit m (q.2, 0))) hc
      rw [hz]
      ring
    · rfl
  map_add' := by
    intro x y
    ext <;> simp [map_add]
  map_smul' := by
    intro c x
    ext <;> simp [map_smul, smul_eq_mul]
  continuous_invFun := by
    have hsplit : Continuous (levelSetSplit m) := (levelSetSplit m).toContinuousLinearEquiv.continuous
    change Continuous (fun q : ℝ × MorseModel m =>
      levelSetSplit m (q.2, (q.1 - (fderiv ℝ (fun v => g (levelSetReindex e v)) w)
        (levelSetSplit m (q.2, 0))) / ((fderiv ℝ (fun v => g (levelSetReindex e v)) w) levelSetLastBasis)))
    exact hsplit.comp (by fun_prop)

noncomputable def levelSetChartMap {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (e : Fin (m + 1) ≃ Fin (m + 1)) : MorseModel (m + 1) → ℝ × MorseModel m :=
  fun w => (g (levelSetReindex e w), levelSetSplitFst m w)

theorem contDiffAt_levelSetChartMap {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (e : Fin (m + 1) ≃ Fin (m + 1)) (w : MorseModel (m + 1))
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g (levelSetReindex e w)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (levelSetChartMap g e) w := by
  have hlin : ContDiffAt ℝ (⊤ : ℕ∞) (fun v : MorseModel (m + 1) => levelSetReindex e v) w :=
    ((levelSetReindex e).toContinuousLinearEquiv :
      MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).contDiff.contDiffAt
  have hg' : ContDiffAt ℝ (⊤ : ℕ∞) (fun v => g (levelSetReindex e v)) w :=
    hg.comp w hlin
  have hp : ContDiffAt ℝ (⊤ : ℕ∞) (fun v : MorseModel (m + 1) => levelSetSplitFst m v) w :=
    (levelSetSplitFst m).contDiff.contDiffAt
  change ContDiffAt ℝ (⊤ : ℕ∞)
    (fun x => (g (levelSetReindex e x), levelSetSplitFst m x)) w
  exact hg'.prodMk hp

theorem contDiff_levelSetChartMap {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (e : Fin (m + 1) ≃ Fin (m + 1)) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (levelSetChartMap g e) := by
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun v : MorseModel (m + 1) => levelSetReindex e v) :=
    ((levelSetReindex e).toContinuousLinearEquiv :
      MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).contDiff
  have hg' : ContDiff ℝ (⊤ : ℕ∞) (fun v => g (levelSetReindex e v)) :=
    hg.comp hlin
  have hp : ContDiff ℝ (⊤ : ℕ∞) (fun v : MorseModel (m + 1) => levelSetSplitFst m v) :=
    (levelSetSplitFst m).contDiff
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => (g (levelSetReindex e x), levelSetSplitFst m x))
  exact hg'.prodMk hp

theorem hasFDerivAt_levelSetChartMap {m : ℕ} (g : MorseModel (m + 1) → ℝ)
    (e : Fin (m + 1) ≃ Fin (m + 1)) (w : MorseModel (m + 1))
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g (levelSetReindex e w))
    (hc : (fderiv ℝ (fun v => g (levelSetReindex e v)) w) levelSetLastBasis ≠ 0) :
    HasFDerivAt (levelSetChartMap g e)
      (↑(levelSetChartDerivEquiv g e w hc) : MorseModel (m + 1) →L[ℝ] (ℝ × MorseModel m)) w := by
  have hdiff : DifferentiableAt ℝ (fun v => g (levelSetReindex e v)) w := by
    have hlin : ContDiffAt ℝ (⊤ : ℕ∞) (fun v : MorseModel (m + 1) => levelSetReindex e v) w :=
      ((levelSetReindex e).toContinuousLinearEquiv :
        MorseModel (m + 1) →L[ℝ] MorseModel (m + 1)).contDiff.contDiffAt
    exact (hg.comp w hlin).differentiableAt (by norm_num)
  have h₁ : HasFDerivAt (fun v => g (levelSetReindex e v))
      (fderiv ℝ (fun v => g (levelSetReindex e v)) w) w :=
    hdiff.hasFDerivAt
  have h₂ : HasFDerivAt (fun v : MorseModel (m + 1) => levelSetSplitFst m v)
      (levelSetSplitFst m) w :=
    (levelSetSplitFst m).hasFDerivAt
  have hpair := h₁.prodMk h₂
  have heq : (fderiv ℝ (fun v => g (levelSetReindex e v)) w).prod (levelSetSplitFst m) =
      ↑(levelSetChartDerivEquiv g e w hc) := by
    ext v <;> rfl
  change HasFDerivAt (fun x => (g (levelSetReindex e x), levelSetSplitFst m x)) _ w
  rw [← heq]
  exact hpair


end R4ModelAtlas
