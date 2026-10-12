import R4Initial.MobiusBand
import R4Initial.Classification07
import R4Embedding.MobiusObstruction
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! Non-orientable normal forms are excluded for smooth orientable surfaces.

A surface homeomorphic to a non-orientable closed normal form contains an open Möbius band
(`R4Initial.MobiusBand`). Smoothing the homeomorphism from the smooth model band onto this open
set near a compact core (chart step of smoothing) and composing with the covering map gives a
smooth immersion of the plane, periodic under a glide reflection; a smooth orientation forbids
it (`not_isOrientableSurface_of_periodic_immersion`). The chart step is an explicit input here;
`R4Initial.RelativeChartSmoothing` proves it. -/

noncomputable section
namespace R4Embedding

open Set Function Filter Topology Manifold R4CoS.Topology.ClassificationOfSurfaces
open scoped ContDiff Manifold

universe u

/-! ### Smoothing near a compact set -/

/-- The chart step smooths a homeomorphism near any compact set. -/
theorem exists_localDiffeomorphOn_of_chartStep {X Y : Type*} [TopologicalSpace X]
    [ChartedSpace Plane X] [TopologicalSpace Y] [ChartedSpace Plane Y]
    (hstep : SmoothingChartStep X Y) (h : X ≃ₜ Y) {K : Set X} (hK : IsCompact K) :
    ∃ g : X ≃ₜ Y, ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧
      IsLocalDiffeomorphOn planeModel planeModel ∞ g V := by
  classical
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace Plane X
  have hC : ∀ x : X, ∃ C : Set X, IsCompact C ∧ x ∈ interior C ∧
      C ⊆ (chartAt Plane x).source :=
    fun x => exists_compact_subset (chartAt Plane x).open_source (mem_chart_source Plane x)
  choose C hCc hCx hCs using hC
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x => interior (C x))
    (fun _ => isOpen_interior) (fun x _ => mem_iUnion.2 ⟨x, hCx x⟩)
  have step : ∀ s : Finset X, ∃ g : X ≃ₜ Y, ∃ V : Set X, IsOpen V ∧
      (⋃ x ∈ s, C x) ⊆ V ∧ IsLocalDiffeomorphOn planeModel planeModel ∞ g V := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨h, ∅, isOpen_empty, by simp, fun x => (notMem_empty _ x.2).elim⟩
    | @insert x s _ ih =>
      obtain ⟨g, V, hV, hsV, hg⟩ := ih
      have hK' : IsCompact (⋃ y ∈ s, C y) := s.isCompact_biUnion fun y _ => hCc y
      obtain ⟨g', V', hV', hKV', hg'⟩ :=
        hstep g _ hK' ⟨V, hV, hsV, hg⟩ x (C x) (hCc x) (hCs x)
      refine ⟨g', V', hV', ?_, hg'⟩
      rw [Finset.set_biUnion_insert]
      exact union_subset (subset_union_right.trans hKV') (subset_union_left.trans hKV')
  obtain ⟨g, V, hV, hsV, hg⟩ := step t
  refine ⟨g, V, hV, fun y hy => hsV ?_, hg⟩
  have hy' := ht hy
  rw [mem_iUnion₂] at hy'
  obtain ⟨x, hxt, hyx⟩ := hy'
  exact mem_biUnion hxt (interior_subset hyx)

/-! ### The strip map and the glide -/

/-- The plane onto the open strip `|u| < 1`, compatible with the glide. -/
def stripMap (v : Plane) : Plane :=
  (v 0) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
    (bandWidth (v 1)) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

@[simp] theorem stripMap_apply_zero (v : Plane) : stripMap v 0 = v 0 := by
  simp [stripMap]

@[simp] theorem stripMap_apply_one (v : Plane) : stripMap v 1 = bandWidth (v 1) := by
  simp [stripMap]

theorem hasDerivAt_bandWidth (u : ℝ) :
    HasDerivAt bandWidth (2 / Real.pi * (1 / (1 + u ^ 2))) u :=
  (Real.hasDerivAt_arctan u).const_mul (2 / Real.pi)

theorem contDiff_bandWidth : ContDiff ℝ ∞ bandWidth :=
  contDiff_const.mul Real.contDiff_arctan

theorem contDiff_stripMap : ContDiff ℝ ∞ stripMap :=
  ((EuclideanSpace.proj (0 : Fin 2)).contDiff.smul contDiff_const).add
    ((contDiff_bandWidth.comp (EuclideanSpace.proj (1 : Fin 2)).contDiff).smul contDiff_const)

/-- The derivative of the strip map. -/
def stripDeriv (v : Plane) : Plane →L[ℝ] Plane :=
  (EuclideanSpace.proj (0 : Fin 2)).smulRight (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) +
    ((2 / Real.pi * (1 / (1 + v 1 ^ 2))) • EuclideanSpace.proj (1 : Fin 2)).smulRight
      (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))

theorem hasFDerivAt_stripMap (v : Plane) : HasFDerivAt stripMap (stripDeriv v) v := by
  have h0 := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt (x := v)
  have h1 := (hasDerivAt_bandWidth (v 1)).comp_hasFDerivAt v
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt
  exact (h0.smul_const _).add (h1.smul_const _)

theorem stripDeriv_injective (v : Plane) : Injective (stripDeriv v) := by
  intro w w' h
  have hc : 0 < 2 / Real.pi * (1 / (1 + v 1 ^ 2)) := by positivity
  have h0 := congrArg (fun x : Plane => x 0) h
  have h1 : stripDeriv v w 1 = stripDeriv v w' 1 := congrArg (fun x : Plane => x 1) h
  have hw1 : ∀ x : Plane,
      stripDeriv v x 1 = (2 / Real.pi * (1 / (1 + v 1 ^ 2))) * x 1 := by
    intro x
    simp [stripDeriv]
  rw [hw1, hw1] at h1
  simp [stripDeriv] at h0
  exact plane_ext h0 (mul_left_cancel₀ hc.ne' h1)

theorem mfderiv_stripMap_injective (v : Plane) :
    Injective (mfderiv planeModel planeModel stripMap v) := by
  have hd : ∀ w, mfderiv planeModel planeModel stripMap v w = stripDeriv v w := by
    intro w
    rw [mfderiv_eq_fderiv, (hasFDerivAt_stripMap v).fderiv]
    rfl
  intro w w' h
  rw [hd, hd] at h
  exact stripDeriv_injective v h

theorem stripMap_glide (v : Plane) :
    stripMap (glideMap 1 v) = Glide.ofShift 1 • stripMap v := by
  rw [glide_smul_def, Glide.shift_ofShift]
  refine plane_ext ?_ ?_
  · simp
  · simp only [stripMap_apply_one, glideMap_apply_one, zpow_one, neg_one_mul, bandWidth_neg]

theorem glideLinear_one_involutive (v : Plane) : glideLinear 1 (glideLinear 1 v) = v := by
  refine plane_ext ?_ ?_
  · simp [glideLinear]
  · simp [glideLinear]

/-- The glide reflection's linear part as an equivalence. -/
def glideEquiv : Plane ≃L[ℝ] Plane :=
  ContinuousLinearEquiv.equivOfInverse (glideLinear 1) (glideLinear 1)
    glideLinear_one_involutive glideLinear_one_involutive

theorem glideEquiv_apply_add (v : Plane) :
    glideEquiv v + ((1 : ℤ) : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) = glideMap 1 v :=
  rfl

theorem det_glideEquiv_neg :
    LinearMap.det ((glideEquiv : Plane →L[ℝ] Plane) : Plane →ₗ[ℝ] Plane) < 0 := by
  have hdet : LinearMap.det ((glideEquiv : Plane →L[ℝ] Plane) : Plane →ₗ[ℝ] Plane) = -1 := by
    rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
      Matrix.det_fin_two]
    simp [LinearMap.toMatrix_apply, glideEquiv, glideLinear]
  rw [hdet]
  norm_num

/-! ### The Möbius band forbids a smooth orientation -/

theorem stripMap_mem_core (v : Plane) :
    mobiusMk (stripMap v) ∈ mobiusMk '' {w : Plane | w 0 ∈ Icc (0 : ℝ) 1 ∧ w 1 ∈ Icc (-1 : ℝ) 1} := by
  refine ⟨Glide.ofShift (-⌊v 0⌋) • stripMap v, ⟨?_, ?_⟩, mobiusMk_smul _ _⟩
  · rw [glide_smul_apply_zero, Glide.shift_ofShift, stripMap_apply_zero]
    push_cast
    constructor
    · linarith [Int.floor_le (v 0)]
    · linarith [Int.lt_floor_add_one (v 0)]
  · rw [glide_smul_apply_one, stripMap_apply_one]
    have h := abs_bandWidth_lt (v 1)
    have habs : |(-1 : ℝ) ^ (Glide.shift (Glide.ofShift (-⌊v 0⌋))) * bandWidth (v 1)| < 1 := by
      rw [abs_mul, abs_neg_one_zpow, one_mul]
      exact h
    rw [abs_lt] at habs
    exact ⟨habs.1.le, habs.2.le⟩

theorem isCompact_core :
    IsCompact {w : Plane | w 0 ∈ Icc (0 : ℝ) 1 ∧ w 1 ∈ Icc (-1 : ℝ) 1} := by
  have himg : IsCompact ((fun x : ℝ × ℝ =>
      x.1 • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
        x.2 • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) '' (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)) :=
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  refine himg.of_isClosed_subset ((isClosed_Icc.preimage (continuous_coord 0)).inter
    (isClosed_Icc.preimage (continuous_coord 1))) ?_
  rintro v ⟨h₀, h₁⟩
  exact ⟨(v 0, v 1), ⟨h₀, h₁⟩, plane_ext (by simp) (by simp)⟩

/-- An open Möbius band in a smooth surface forbids a smooth orientation, given the chart step
of smoothing onto open subsets. -/
theorem not_isOrientableSurface_of_mobiusBand {M : Type*} [TopologicalSpace M]
    [ChartedSpace Plane M] [IsManifold planeModel ∞ M] (f : MobiusBand → M)
    (hf : IsOpenEmbedding f)
    (hstep : ∀ (U : TopologicalSpace.Opens M) [T2Space U], SmoothingChartStep MobiusBand U) :
    ¬ IsOrientableSurface M := by
  classical
  let U : TopologicalSpace.Opens M := ⟨range f, hf.isOpen_range⟩
  let e : MobiusBand ≃ₜ U := hf.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr rfl)
  have : T2Space U := e.symm.isEmbedding.t2Space
  obtain ⟨g, V, hV, hKV, hg⟩ := exists_localDiffeomorphOn_of_chartStep (hstep U) e
    (isCompact_core.image continuous_mobiusMk)
  have hq := MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
    (G := Glide) (M := Plane) planeModel (n := ∞)
  have hloc : ∀ v : Plane,
      IsLocalDiffeomorphAt planeModel planeModel ∞ (g ∘ mobiusMk) (stripMap v) := fun v =>
    IsLocalDiffeomorphAt.comp (K := planeModel) (P := U) (hq (stripMap v))
      (hg ⟨_, hKV (stripMap_mem_core v)⟩)
  let φ : Plane → M := fun v => ((g (mobiusMk (stripMap v)) : U) : M)
  have hφeq : φ = Subtype.val ∘ ((g ∘ mobiusMk) ∘ stripMap) := rfl
  have hstrip : ContMDiff planeModel planeModel ∞ stripMap := contDiff_stripMap.contMDiff
  have hφ : ContMDiff planeModel planeModel 1 φ := by
    intro v
    rw [hφeq]
    exact (contMDiff_subtype_val.contMDiffAt).comp v
      (((hloc v).contMDiffAt.of_le (by simp)).comp v ((hstrip v).of_le (by simp)))
  have hinj : ∀ v, Injective (mfderiv planeModel planeModel φ v) := by
    intro v
    have hd1 : MDifferentiableAt planeModel planeModel (Subtype.val : U → M)
        ((g ∘ mobiusMk) (stripMap v)) :=
      (contMDiff_subtype_val (n := ∞)).contMDiffAt.mdifferentiableAt (by simp)
    have hd2 : MDifferentiableAt planeModel planeModel (g ∘ mobiusMk) (stripMap v) :=
      (hloc v).mdifferentiableAt (by simp)
    have hd3 : MDifferentiableAt planeModel planeModel stripMap v :=
      (hstrip v).mdifferentiableAt (by simp)
    rw [hφeq, mfderiv_comp v hd1 (hd2.comp v hd3), mfderiv_comp v hd2 hd3]
    obtain ⟨E, hE⟩ := (hloc v).isInvertible_mfderiv (by simp)
    have i1 : Injective (mfderiv planeModel planeModel (Subtype.val : U → M)
        ((g ∘ mobiusMk) (stripMap v))) :=
      (IsImmersion.of_opens (I := planeModel) (n := ∞) U).injective_mfderiv (by simp) _
    have i2 : Injective (mfderiv planeModel planeModel (g ∘ mobiusMk) (stripMap v)) := by
      rw [← hE]
      exact E.injective
    exact i1.comp (i2.comp (mfderiv_stripMap_injective v))
  have hper : ∀ v, φ (glideEquiv v + ((1 : ℤ) : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) =
      φ v := by
    intro v
    simp only [φ, glideEquiv_apply_add, stripMap_glide, mobiusMk_smul]
  exact not_isOrientableSurface_of_periodic_immersion φ hφ hinj glideEquiv det_glideEquiv_neg _
    hper

/-- The non-orientable closed normal forms are excluded, given the chart step of smoothing
onto open subsets of surfaces. -/
theorem noNonOrientableNormalFormStatement_of_chartStep
    (hstep : ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace Plane M]
      [IsManifold planeModel ∞ M] (U : TopologicalSpace.Opens M) [T2Space U],
      SmoothingChartStep MobiusBand U) :
    NoNonOrientableNormalFormStatement.{u} := by
  intro M _ _ _ horient p hp
  refine ⟨fun h => ?_⟩
  obtain ⟨f, hf⟩ := exists_isOpenEmbedding_mobiusBand hp h
  exact not_isOrientableSurface_of_mobiusBand f hf (hstep M) horient

end R4Embedding
