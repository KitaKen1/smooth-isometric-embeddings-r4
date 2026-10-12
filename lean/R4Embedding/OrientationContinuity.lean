import R4Embedding.SurfaceOrientation

/-! Orientation continuity from an actual nonvanishing top-degree form.
For the polynomial models the remaining input is continuity of its coefficient
in every actual chart; pointwise existence of orientations is insufficient.
-/

set_option autoImplicit false
noncomputable section
namespace R4Embedding

open Set Manifold Module
open scoped Topology ContDiff

theorem locallyConstant_ray_of_forms
    {X V ι : Type*} [TopologicalSpace X] [AddCommGroup V] [Module ℝ V]
    [Fintype ι] [DecidableEq ι] (e : Basis ι ℝ V)
    (A : X → V [⋀^ι]→ₗ[ℝ] ℝ) (hne : ∀ x, A x ≠ 0)
    (hc : Continuous (fun x => A x e)) :
    IsLocallyConstant (fun x => rayOfNeZero ℝ (A x) (hne x)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  have hx : A x e ≠ 0 := ((A x).map_basis_ne_zero_iff e).mpr (hne x)
  have hp : 0 < A x e * A x e := mul_self_pos.mpr hx
  have ht : ContinuousAt (fun y => A y e * A x e) x :=
    hc.continuousAt.mul continuousAt_const
  have he : ∀ᶠ y in 𝓝 x, 0 < A y e * A x e :=
    ht.preimage_mem_nhds (isOpen_Ioi.mem_nhds hp)
  filter_upwards [he] with y hy
  apply (ray_eq_iff (hne y) (hne x)).mpr
  rw [(A y).eq_smul_basis_det e, (A x).eq_smul_basis_det e]
  exact sameRay_smul_smul_of_mul_nonneg hy.le

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

def surfaceChartArea
    (A : M → Plane [⋀^Fin 2]→ₗ[ℝ] ℝ) (p : M) (x : (chartAt Plane p).source) :
    Plane [⋀^Fin 2]→ₗ[ℝ] ℝ :=
  (A x.val).compLinearMap
    (preferredSurfaceChartEquiv p x.val x.property).toLinearEquiv.symm.toLinearMap

theorem surfaceChartArea_ne_zero
    (A : M → Plane [⋀^Fin 2]→ₗ[ℝ] ℝ) (hne : ∀ x, A x ≠ 0)
    (p : M) (x : (chartAt Plane p).source) : surfaceChartArea A p x ≠ 0 :=
  mt ((A x.val).compLinearEquiv_eq_zero_iff
    (preferredSurfaceChartEquiv p x.val x.property).toLinearEquiv.symm).mp (hne x.val)

def surfaceOrientationOfForms
    (e : Basis (Fin 2) ℝ Plane)
    (A : M → Plane [⋀^Fin 2]→ₗ[ℝ] ℝ) (hne : ∀ x, A x ≠ 0)
    (hc : ∀ p, Continuous (fun x : (chartAt Plane p).source => surfaceChartArea A p x e)) :
    SurfaceOrientation M := by
  refine ⟨fun x => rayOfNeZero ℝ (A x) (hne x), ?_⟩
  intro p
  have h := locallyConstant_ray_of_forms e (surfaceChartArea A p)
    (surfaceChartArea_ne_zero A hne p) (hc p)
  simpa only [Orientation.map_apply, surfaceChartArea] using h

theorem isOrientableSurface_of_forms
    (e : Basis (Fin 2) ℝ Plane)
    (A : M → Plane [⋀^Fin 2]→ₗ[ℝ] ℝ) (hne : ∀ x, A x ≠ 0)
    (hc : ∀ p, Continuous (fun x : (chartAt Plane p).source => surfaceChartArea A p x e)) :
    IsOrientableSurface M :=
  ⟨surfaceOrientationOfForms e A hne hc⟩

end R4Embedding
