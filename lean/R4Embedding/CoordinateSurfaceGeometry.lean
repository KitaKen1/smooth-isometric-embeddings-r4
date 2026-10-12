import R4Embedding.SmoothProfileAtlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! The old surface fields are genuine first and second derivatives of one
coordinate representation. Smoothness supplies their continuity; only the
centre's tangent injectivity and Gauss condition remain geometric inputs. -/

noncomputable section

namespace R4Embedding

open Bundle Manifold
open scoped ContDiff

def coordinateSurfaceX (G : (ℝ × ℝ) → Space) (q : ℝ × ℝ) : Space :=
  fderiv ℝ G q (1, 0)

def coordinateSurfaceY (G : (ℝ × ℝ) → Space) (q : ℝ × ℝ) : Space :=
  fderiv ℝ G q (0, 1)

def coordinateSurfaceYY (G : (ℝ × ℝ) → Space) (q : ℝ × ℝ) : Space :=
  fderiv ℝ (coordinateSurfaceY G) q (0, 1)

theorem surfaceTangentMap_of_coordinate_derivative (T : (ℝ × ℝ) →L[ℝ] Space) :
    surfaceTangentMap (T (1, 0)) (T (0, 1)) = T := by
  apply ContinuousLinearMap.ext
  intro q
  change q.1 • T (1, 0) + q.2 • T (0, 1) = T q
  have hq : q = q.1 • (1, 0) + q.2 • (0, 1) := by
    ext <;> simp
  simpa only [map_add, map_smul] using (congrArg T hq).symm

theorem coordinateSurfaceX_contDiffAt {G : (ℝ × ℝ) → Space} {q : ℝ × ℝ}
    (hG : ContDiffAt ℝ ∞ G q) : ContDiffAt ℝ ∞ (coordinateSurfaceX G) q :=
  (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

theorem coordinateSurfaceY_contDiffAt {G : (ℝ × ℝ) → Space} {q : ℝ × ℝ}
    (hG : ContDiffAt ℝ ∞ G q) : ContDiffAt ℝ ∞ (coordinateSurfaceY G) q :=
  (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

theorem coordinateSurfaceYY_contDiffAt {G : (ℝ × ℝ) → Space} {q : ℝ × ℝ}
    (hG : ContDiffAt ℝ ∞ G q) : ContDiffAt ℝ ∞ (coordinateSurfaceYY G) q :=
  ((coordinateSurfaceY_contDiffAt hG).fderiv_right (m := ∞) (by simp)).clm_apply
    contDiffAt_const

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
theorem coordinate_surface_contDiffAt {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (e : OpenPartialHomeomorph M (ℝ × ℝ))
    (he : ContMDiffOn pairModel planeModel ∞ e.symm e.target)
    {p : M} (hp : p ∈ e.source) : ContDiffAt ℝ ∞ (F ∘ e.symm) (e p) := by
  have hc := (he (e p) (e.map_source hp)).contMDiffAt
    (e.open_target.mem_nhds (e.map_source hp))
  exact (hF.contMDiffAt.comp (e p) hc).contDiffAt

/-- This factory ties all old derivative fields to F. It does not supply
the Gauss coefficient, coordinate tangent injectivity, or an initial F. -/
def geometryOfCoordinateSurface {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (e : OpenPartialHomeomorph M (ℝ × ℝ))
    (he : ContMDiffOn pairModel planeModel ∞ e.symm e.target)
    {p : M} (hp : p ∈ e.source)
    (hinj : Function.Injective (fderiv ℝ (F ∘ e.symm) (e p)))
    (normal : Space) (k l : ℝ)
    (hgauss : coordinateSurfaceYY (F ∘ e.symm) (e p) =
      k • coordinateSurfaceX (F ∘ e.symm) (e p) +
      l • coordinateSurfaceY (F ∘ e.symm) (e p) + normal)
    (hk : k ≠ 0)
    (hnu : inner ℝ (coordinateSurfaceX (F ∘ e.symm) (e p)) normal = 0)
    (hnv : inner ℝ (coordinateSurfaceY (F ∘ e.symm) (e p)) normal = 0) :
    SmoothSurfaceProfileGeometry M p where
  toSurfaceProfileGeometry := {
    chart := e
    mem_source := hp
    u := coordinateSurfaceX (F ∘ e.symm)
    v := coordinateSurfaceY (F ∘ e.symm)
    acc := coordinateSurfaceYY (F ∘ e.symm)
    u_continuous := (coordinateSurfaceX_contDiffAt
      (coordinate_surface_contDiffAt hF e he hp)).continuousAt
    v_continuous := (coordinateSurfaceY_contDiffAt
      (coordinate_surface_contDiffAt hF e he hp)).continuousAt
    acc_continuous := (coordinateSurfaceYY_contDiffAt
      (coordinate_surface_contDiffAt hF e he hp)).continuousAt
    tangent_injective := by
      change Function.Injective (surfaceTangentMap
        (fderiv ℝ (F ∘ e.symm) (e p) (1, 0))
        (fderiv ℝ (F ∘ e.symm) (e p) (0, 1)))
      rw [surfaceTangentMap_of_coordinate_derivative]
      exact hinj
    normal := normal
    k := k
    l := l
    gauss := hgauss
    k_ne_zero := hk
    normal_u := hnu
    normal_v := hnv }
  smooth_inverse := he

end R4Embedding
