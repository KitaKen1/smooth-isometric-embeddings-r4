import R4Embedding.ComponentAssembly
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.LinearAlgebra.Orientation
import Mathlib.Topology.LocallyConstant.Basic

/-!
Surface orientations expressed in the actual preferred tangent charts.
Adapted and specialized from qinz1yang/differential-geometry, Apache-2.0,
commit bafefb7ce5ce7e40417641d67e6e95727b7bba1f:
Topology/Manifold/{OpenSubtype,SmoothOrientation,SmoothOrientationOpen}.lean.
The adaptation fixes the surface model and ports the declarations to Lean 4.34.1.
-/

noncomputable section
namespace R4Embedding

open Set Function Manifold TopologicalSpace
open scoped Manifold ContDiff Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem hasMFDerivAt_openSubtype_val (U : Opens M) (p : U) :
    HasMFDerivAt planeModel planeModel (Subtype.val : U → M) p
      (ContinuousLinearMap.id ℝ Plane) := by
  constructor
  · exact continuous_subtype_val.continuousAt
  · let e : OpenPartialHomeomorph U Plane :=
      (chartAt Plane p.val).subtypeRestr (s := U) (⟨p⟩ : Nonempty U)
    apply HasFDerivWithinAt.congr_of_eventuallyEq (hasFDerivWithinAt_id _ _)
    · apply Filter.eventuallyEq_of_mem (extChartAt_target_mem_nhdsWithin (I := planeModel) p)
      intro y hy
      have he : planeModel.symm y ∈ e.target := by
        simpa [e, extChartAt, Opens.chartAt_eq] using hy
      have hright := e.right_inv he
      simp only [writtenInExtChartAt, Function.comp_apply, id_eq]
      change (chartAt Plane p.val) ((e.symm y).val) = y
      exact hright
    · simp only [writtenInExtChartAt, Function.comp_apply, id_eq]
      have hleft := (extChartAt planeModel p).left_inv (mem_extChartAt_source p)
      rw [hleft]
      rfl

theorem mfderiv_openSubtype_val (U : Opens M) (p : U) :
    mfderiv planeModel planeModel (Subtype.val : U → M) p =
      ContinuousLinearMap.id ℝ Plane :=
  (hasMFDerivAt_openSubtype_val U p).mfderiv

variable [IsManifold planeModel ∞ M]

def preferredSurfaceChartEquiv (p x : M) (hx : x ∈ (chartAt Plane p).source) :
    Plane ≃L[ℝ] Plane := by
  let D : Plane →L[ℝ] Plane := mfderiv planeModel planeModel (extChartAt planeModel p) x
  have hi : Injective D :=
    (isInvertible_mfderiv_extChartAt (I := planeModel)
      (by simpa only [extChartAt_source] using hx)).injective
  exact (D.toLinearMap.linearEquivOfInjective hi rfl).toContinuousLinearEquiv

theorem preferredSurfaceChartEquiv_apply (p x : M) (hx : x ∈ (chartAt Plane p).source)
    (v : Plane) :
    preferredSurfaceChartEquiv p x hx v = mfderiv planeModel planeModel
      (extChartAt planeModel p) x v := rfl

/-- A tangent orientation locally constant when read in each actual chart.
Its existence is independent of any initial embedding. -/
def SurfaceOrientation (M : Type*) [TopologicalSpace M] [ChartedSpace Plane M]
    [IsManifold planeModel ∞ M] : Type _ :=
  {o : M → Orientation ℝ Plane (Fin 2) //
    ∀ p : M, IsLocallyConstant (fun x : (chartAt Plane p).source =>
      Orientation.map (Fin 2)
        (preferredSurfaceChartEquiv p x.val x.property).toLinearEquiv (o x.val))}

def IsOrientableSurface (M : Type*) [TopologicalSpace M] [ChartedSpace Plane M]
    [IsManifold planeModel ∞ M] : Prop := Nonempty (SurfaceOrientation M)

theorem preferredSurfaceChartEquiv_open (U : Opens M) (p x : U)
    (hx : x ∈ (chartAt Plane p).source) :
    preferredSurfaceChartEquiv p x hx = preferredSurfaceChartEquiv p.val x.val hx.2 := by
  apply ContinuousLinearEquiv.ext
  funext v
  have h := mfderiv_comp (f := (Subtype.val : U → M))
    (g := (extChartAt planeModel p.val : M → Plane)) x
    (mdifferentiableAt_extChartAt (I := planeModel) hx.2)
    ((contMDiff_subtype_val (I := planeModel) (U := U) (n := ∞)).mdifferentiableAt (by simp))
  rw [mfderiv_openSubtype_val] at h
  exact congrArg (fun A : Plane →L[ℝ] Plane => A v) h

def restrictSurfaceOrientation (U : Opens M) (o : SurfaceOrientation M) :
    SurfaceOrientation U := by
  refine ⟨fun x => o.val x.val, ?_⟩
  intro p
  let a : (chartAt Plane p).source → (chartAt Plane p.val).source :=
    fun x => ⟨x.val.val, x.property.2⟩
  have ha : Continuous a :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have h := (o.property p.val).comp_continuous ha
  have he : (fun x : (chartAt Plane p).source =>
      Orientation.map (Fin 2)
        (preferredSurfaceChartEquiv p x.val x.property).toLinearEquiv (o.val x.val.val)) =
      (fun x : (chartAt Plane p).source => Orientation.map (Fin 2)
        (preferredSurfaceChartEquiv p.val (a x).val (a x).property).toLinearEquiv
          (o.val (a x).val)) := by
    funext x
    rw [preferredSurfaceChartEquiv_open]
  rw [he]
  exact h

theorem restrictSurfaceOrientation_apply (U : Opens M) (o : SurfaceOrientation M) (x : U) :
    (restrictSurfaceOrientation U o).val x = o.val x.val := rfl

theorem isOrientableSurface_open (U : Opens M) (h : IsOrientableSurface M) :
    IsOrientableSurface U := by
  obtain ⟨o⟩ := h
  exact ⟨restrictSurfaceOrientation U o⟩

theorem isOrientableSurface_component (c : ConnectedComponents M)
    (h : IsOrientableSurface M) : IsOrientableSurface (componentOpen c) :=
  isOrientableSurface_open (componentOpen c) h

end R4Embedding
