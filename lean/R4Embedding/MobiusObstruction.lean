import R4Embedding.SurfaceOrientation

/-! A smooth orientation forbids a Möbius-periodic immersion of the plane. This is
the smooth half of excluding non-orientable normal forms: pulled back along such an
immersion, the orientation is a determinant sign, locally constant on the connected
plane, while the deck map `v ↦ L v + a` with `det L < 0` reverses it. Producing such
an immersion from a homeomorphism to a non-orientable model is a separate step. -/

noncomputable section
namespace R4Embedding

open Manifold Set Filter Function
open scoped ContDiff Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

/-- Two units of the same sign act identically on a ray. -/
theorem orientation_units_smul_eq_of_sign {x : Orientation ℝ Plane (Fin 2)} {u w : ℝˣ}
    (h : 0 < (u : ℝ) ↔ 0 < (w : ℝ)) : u • x = w • x := by
  rcases lt_or_gt_of_ne u.ne_zero with hu | hu
  · have hw : (w : ℝ) < 0 := by
      rcases lt_or_gt_of_ne w.ne_zero with hw | hw
      · exact hw
      · exact absurd (h.2 hw) (not_lt.2 hu.le)
    rw [Module.Ray.units_smul_of_neg u hu, Module.Ray.units_smul_of_neg w hw]
  · rw [Module.Ray.units_smul_of_pos u hu, Module.Ray.units_smul_of_pos w (h.1 hu)]

theorem not_isOrientableSurface_of_periodic_immersion
    (φ : Plane → M) (hφ : ContMDiff planeModel planeModel 1 φ)
    (hinj : ∀ v, Function.Injective (mfderiv planeModel planeModel φ v))
    (L : Plane ≃L[ℝ] Plane) (hL : LinearMap.det (L : Plane →ₗ[ℝ] Plane) < 0) (a : Plane)
    (hper : ∀ v, φ (L v + a) = φ v) :
    ¬ IsOrientableSurface M := by
  rintro ⟨o⟩
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ Plane := by simp
  let D : Plane → (Plane →ₗ[ℝ] Plane) := fun v =>
    show Plane →ₗ[ℝ] Plane from (mfderiv planeModel planeModel φ v).toLinearMap
  have hD : ∀ v, Function.Injective (D v) := fun v x y h => hinj v h
  let e : Plane → (Plane ≃ₗ[ℝ] Plane) := fun v =>
    LinearEquiv.ofInjectiveEndo (D v) (hD v)
  have he : ∀ v, ((LinearEquiv.det (e v) : ℝˣ) : ℝ) = LinearMap.det (D v) := by
    intro v
    rw [LinearEquiv.coe_det]
    congr 1
  -- the orientation pulled back to the plane
  let ψ : Plane → Orientation ℝ Plane (Fin 2) := fun v => LinearEquiv.det (e v) • o.1 (φ v)
  -- the deck transformation reverses it
  have hderiv : ∀ v, mfderiv planeModel planeModel φ v =
      (mfderiv planeModel planeModel φ (L v + a)).comp (L : Plane →L[ℝ] Plane) := by
    intro v
    have hT : HasFDerivAt (fun w : Plane => L w + a) (L : Plane →L[ℝ] Plane) v :=
      L.hasFDerivAt.add_const a
    have hTm : MDifferentiableAt planeModel planeModel (fun w : Plane => L w + a) v :=
      hT.differentiableAt.mdifferentiableAt
    have hcomp : φ = φ ∘ fun w => L w + a := funext fun w => (hper w).symm
    conv_lhs => rw [hcomp]
    rw [mfderiv_comp v ((hφ (L v + a)).mdifferentiableAt (by simp)) hTm, mfderiv_eq_fderiv,
      hT.fderiv]
    rfl
  have hrev : ∀ v, ψ v = -ψ (L v + a) := by
    intro v
    have hdet : LinearEquiv.det (e v) =
        LinearEquiv.det L.toLinearEquiv * LinearEquiv.det (e (L v + a)) := by
      ext
      rw [Units.val_mul, he v, he (L v + a), LinearEquiv.coe_det]
      have h := congrArg (fun f : Plane →L[ℝ] Plane => (f : Plane →ₗ[ℝ] Plane)) (hderiv v)
      change LinearMap.det (D v) = _
      rw [show D v = D (L v + a) ∘ₗ (L : Plane →ₗ[ℝ] Plane) from h, LinearMap.det_comp,
        mul_comm]
    have hneg : ((LinearEquiv.det L.toLinearEquiv : ℝˣ) : ℝ) < 0 := by
      rw [LinearEquiv.coe_det]
      exact hL
    change LinearEquiv.det (e v) • o.1 (φ v) = -(LinearEquiv.det (e (L v + a)) • o.1 (φ (L v + a)))
    rw [hper v, hdet, mul_smul, Module.Ray.units_smul_of_neg _ hneg]
  -- ψ is locally constant
  have hloc : IsLocallyConstant ψ := by
    refine (IsLocallyConstant.iff_eventually_eq ψ).2 fun v₀ => ?_
    set p := φ v₀ with hpdef
    let s := (chartAt Plane p).source
    have hs : IsOpen s := (chartAt Plane p).open_source
    have hp : p ∈ s := mem_chart_source Plane p
    let κ : s → Orientation ℝ Plane (Fin 2) := fun x =>
      Orientation.map (Fin 2) (preferredSurfaceChartEquiv p x.1 x.2).toLinearEquiv (o.1 x.1)
    have hκ : IsLocallyConstant κ := o.2 p
    have hoκ : ∀ x : s, o.1 x.1 =
        LinearEquiv.det (preferredSurfaceChartEquiv p x.1 x.2).toLinearEquiv • κ x := by
      intro x
      change o.1 x.1 = _ • Orientation.map (Fin 2) _ (o.1 x.1)
      rw [Orientation.map_eq_det_inv_smul _ _ hcard, smul_inv_smul]
    -- near v₀ the point stays in the chart and the chart orientation is constant
    have hU : ∀ᶠ v in 𝓝 v₀, φ v ∈ s :=
      hφ.continuous.continuousAt.preimage_mem_nhds (hs.mem_nhds hp)
    have hK : ∀ᶠ v in 𝓝 v₀, ∀ y : s, y.1 = φ v → κ y = κ ⟨p, hp⟩ := by
      have h := (IsLocallyConstant.iff_eventually_eq κ).1 hκ ⟨p, hp⟩
      rw [nhds_subtype_eq_comap, Filter.eventually_comap] at h
      exact (hφ.continuous.tendsto v₀).eventually h
    -- the determinant of the chart-composite derivative has locally constant sign
    let F : Plane → Plane := extChartAt planeModel p ∘ φ
    have hUo : IsOpen (φ ⁻¹' s) := hs.preimage hφ.continuous
    have hv₀ : v₀ ∈ φ ⁻¹' s := hp
    have hF : ContDiffOn ℝ 1 F (φ ⁻¹' s) := by
      have hc : ContMDiffOn planeModel planeModel 1 (extChartAt planeModel p) s :=
        (contMDiffOn_extChartAt (I := planeModel) (n := ∞) (x := p)).of_le (by simp)
      exact contMDiffOn_iff_contDiffOn.1 (hc.comp hφ.contMDiffOn fun v hv => hv)
    have hFd : ContinuousAt (fun v => (fderiv ℝ F v).det) v₀ :=
      ContinuousLinearMap.continuous_det.continuousAt.comp
        ((hF.continuousOn_fderiv_of_isOpen hUo le_rfl).continuousAt (hUo.mem_nhds hv₀))
    have hdetF : ∀ v (hv : φ v ∈ s), (fderiv ℝ F v).det =
        ((LinearEquiv.det (preferredSurfaceChartEquiv p (φ v) hv).toLinearEquiv *
          LinearEquiv.det (e v) : ℝˣ) : ℝ) := by
      intro v hv
      have hcomp : fderiv ℝ F v = (mfderiv planeModel planeModel (extChartAt planeModel p) (φ v)).comp
          (mfderiv planeModel planeModel φ v) := by
        rw [← mfderiv_eq_fderiv]
        exact mfderiv_comp v (mdifferentiableAt_extChartAt hv) ((hφ v).mdifferentiableAt (by simp))
      have hlin : ((fderiv ℝ F v : Plane →L[ℝ] Plane) : Plane →ₗ[ℝ] Plane) =
          (show Plane →ₗ[ℝ] Plane from
            (mfderiv planeModel planeModel (extChartAt planeModel p) (φ v)).toLinearMap) ∘ₗ D v := by
        rw [hcomp]
        rfl
      change LinearMap.det ((fderiv ℝ F v : Plane →L[ℝ] Plane) : Plane →ₗ[ℝ] Plane) = _
      rw [hlin, LinearMap.det_comp, Units.val_mul, he v, LinearEquiv.coe_det]
      congr 2
    have hsign : ∀ᶠ v in 𝓝 v₀, (0 < (fderiv ℝ F v).det ↔ 0 < (fderiv ℝ F v₀).det) := by
      have hne : (fderiv ℝ F v₀).det ≠ 0 := by
        rw [hdetF v₀ hp]
        exact Units.ne_zero _
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · filter_upwards [hFd.eventually (gt_mem_nhds hneg)] with v hv
        exact ⟨fun h => absurd h (not_lt.2 hv.le), fun h => absurd h (not_lt.2 hneg.le)⟩
      · filter_upwards [hFd.eventually (lt_mem_nhds hpos)] with v hv
        exact ⟨fun _ => hpos, fun _ => hv⟩
    filter_upwards [hU, hK, hsign] with v hv hKv hsv
    have hψ : ∀ w (hw : φ w ∈ s), κ ⟨φ w, hw⟩ = κ ⟨p, hp⟩ →
        ψ w = (LinearEquiv.det (preferredSurfaceChartEquiv p (φ w) hw).toLinearEquiv *
          LinearEquiv.det (e w)) • κ ⟨p, hp⟩ := by
      intro w hw hk
      change LinearEquiv.det (e w) • o.1 (φ w) = _
      rw [hoκ ⟨φ w, hw⟩, hk, smul_smul, mul_comm]
    rw [hψ v hv (hKv ⟨φ v, hv⟩ rfl), hψ v₀ hp rfl]
    apply orientation_units_smul_eq_of_sign
    rw [← hdetF v hv, ← hdetF v₀ hp]
    exact hsv
  have hc : ψ 0 = ψ (L 0 + a) := hloc.apply_eq_of_preconnectedSpace _ _
  have h0 := hrev 0
  rw [hc] at h0
  exact Module.Ray.ne_neg_self _ h0

end R4Embedding
