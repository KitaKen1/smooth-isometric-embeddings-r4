import R4Embedding.OrientationContinuity
import Mathlib.LinearAlgebra.Alternating.Curry
import R4Embedding.PolynomialNormal
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The area induced by a smooth immersion and a continuous transverse field
has continuous coefficients in the actual preferred surface charts.
-/
set_option autoImplicit false
noncomputable section
namespace R4Embedding
open Set Manifold Module Function
open scoped ContDiff Topology Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

def immersionSurfaceArea (f : M → ModelAmbient) (N : M → ModelAmbient) (x : M) :
    Plane [⋀^Fin 2]→ₗ[ℝ] ℝ :=
  (((Pi.basisFun ℝ (Fin 3)).det).curryLeft (N x)).compLinearMap
    (mfderiv planeModel 𝓘(ℝ, ModelAmbient) f x).toLinearMap

set_option backward.isDefEq.respectTransparency false in
theorem preferredSurfaceChartEquiv_symm_apply (p x : M)
    (hx : x ∈ (chartAt Plane p).source) (v : Plane) :
    (preferredSurfaceChartEquiv p x hx).symm v =
      mfderiv planeModel planeModel (extChartAt planeModel p).symm
        (extChartAt planeModel p x) v := by
  have h := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := planeModel)
    (by simpa only [extChartAt_source] using hx)
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at h
  have hh := congrArg (fun L : Plane →L[ℝ] Plane =>
    L ((preferredSurfaceChartEquiv p x hx).symm v)) h
  change mfderiv planeModel planeModel (extChartAt planeModel p).symm
    (extChartAt planeModel p x)
    ((preferredSurfaceChartEquiv p x hx) ((preferredSurfaceChartEquiv p x hx).symm v)) =
    (preferredSurfaceChartEquiv p x hx).symm v at hh
  simpa only [TangentSpace, ContinuousLinearEquiv.apply_symm_apply] using hh.symm

theorem immersion_in_fixed_chart_derivative
    {f : M → ModelAmbient} (hf : ContMDiff planeModel 𝓘(ℝ, ModelAmbient) ∞ f)
    (p x : M) (hx : x ∈ (chartAt Plane p).source) (v : Plane) :
    mfderiv planeModel 𝓘(ℝ, ModelAmbient) f x
      ((preferredSurfaceChartEquiv p x hx).symm v) =
    fderiv ℝ (f ∘ (extChartAt planeModel p).symm) (extChartAt planeModel p x) v := by
  have ht : extChartAt planeModel p x ∈ (extChartAt planeModel p).target :=
    (extChartAt planeModel p).map_source (by simpa only [extChartAt_source] using hx)
  have hc : ContMDiffAt planeModel planeModel ∞ (extChartAt planeModel p).symm
      (extChartAt planeModel p x) :=
    (contMDiffOn_extChartAt_symm p _ ht).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds ht)
  have h := mfderiv_comp (extChartAt planeModel p x)
    (hf.contMDiffAt.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))
  rw [(extChartAt planeModel p).left_inv (by simpa only [extChartAt_source] using hx),
    mfderiv_eq_fderiv] at h
  rw [preferredSurfaceChartEquiv_symm_apply]
  exact (congrArg (fun L : Plane →L[ℝ] ModelAmbient => L v) h).symm

theorem modelAmbientDet_continuous :
    Continuous (fun v : Fin 3 → ModelAmbient => (Pi.basisFun ℝ (Fin 3)).det v) := by
  simp_rw [Basis.det_apply, Matrix.det_apply']
  apply continuous_finsetSum
  intro σ _
  apply continuous_const.mul
  apply continuous_finsetProd
  intro i _
  exact (continuous_apply i).comp ((continuous_apply (σ i)).comp
    ((Pi.basisFun ℝ (Fin 3)).continuous_toMatrix))

theorem immersionSurfaceChartArea_continuous
    {f : M → ModelAmbient} (hf : ContMDiff planeModel 𝓘(ℝ, ModelAmbient) ∞ f)
    {N : M → ModelAmbient} (hN : Continuous N) (p : M)
    (e : Basis (Fin 2) ℝ Plane) :
    Continuous (fun x : (chartAt Plane p).source =>
      surfaceChartArea (immersionSurfaceArea f N) p x e) := by
  rw [continuous_iff_continuousAt]
  intro x
  have ht : extChartAt planeModel p x.val ∈ (extChartAt planeModel p).target :=
    (extChartAt planeModel p).map_source (by simpa only [extChartAt_source] using x.property)
  have hc : ContMDiffAt planeModel planeModel ∞ (extChartAt planeModel p).symm
      (extChartAt planeModel p x.val) :=
    (contMDiffOn_extChartAt_symm p _ ht).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds ht)
  have hq : ContDiffAt ℝ ∞ (f ∘ (extChartAt planeModel p).symm)
      (extChartAt planeModel p x.val) := (hf.contMDiffAt.comp _ hc).contDiffAt
  have hchart : ContinuousAt (fun y : (chartAt Plane p).source =>
      extChartAt planeModel p y.val) x :=
    (continuousAt_extChartAt' (by simpa only [extChartAt_source] using x.property)).comp
      continuous_subtype_val.continuousAt
  have heval (i : Fin 2) : ContinuousAt (fun y : (chartAt Plane p).source =>
      fderiv ℝ (f ∘ (extChartAt planeModel p).symm) (extChartAt planeModel p y.val) (e i)) x :=
    ((hq.fderiv_right (m := ∞) (by simp)).continuousAt.comp (f := fun y : (chartAt Plane p).source =>
      extChartAt planeModel p y.val) hchart).clm_apply
      continuousAt_const
  have hv : ContinuousAt (fun y : (chartAt Plane p).source =>
      Matrix.vecCons (N y.val) (fun i => fderiv ℝ
        (f ∘ (extChartAt planeModel p).symm) (extChartAt planeModel p y.val) (e i))) x := by
    apply continuousAt_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hN.continuousAt.comp continuous_subtype_val.continuousAt
    · exact heval j
  have hd := modelAmbientDet_continuous.continuousAt.comp hv
  convert hd using 1
  funext y
  change (Pi.basisFun ℝ (Fin 3)).det (Matrix.vecCons (N y.val)
    (fun i => mfderiv planeModel 𝓘(ℝ, ModelAmbient) f y.val
      ((preferredSurfaceChartEquiv p y.val y.property).symm (e i)))) = _
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact immersion_in_fixed_chart_derivative hf p y.val y.property (e j)

end R4Embedding
