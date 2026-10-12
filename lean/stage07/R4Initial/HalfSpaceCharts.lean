import R4Embedding.Problem
import Mathlib.Geometry.Manifold.Instances.Real

/-! Topological charts in the closed half-plane for a surface charted on the plane.
The plane is homeomorphic to the open half-plane through `(x₀, x₁) ↦ (exp x₀, x₁)`;
composing charts gives a `C⁰` manifold modelled on `EuclideanHalfSpace 2`, which is the
input format of the topological classification of compact surfaces. -/

noncomputable section
namespace R4Embedding

open Set Manifold

/-- The open half-plane chart of the plane. -/
def planeHalfChart : OpenPartialHomeomorph Plane (EuclideanHalfSpace 2) where
  toFun x := ⟨WithLp.toLp 2 ![Real.exp (x 0), x 1], by simp [(Real.exp_pos _).le]⟩
  invFun y := WithLp.toLp 2 ![Real.log (y.1 0), y.1 1]
  source := univ
  target := {y | 0 < y.1 0}
  map_source' x _ := by simp [Real.exp_pos]
  map_target' _ _ := mem_univ _
  left_inv' x _ := by
    ext i
    fin_cases i <;> simp
  right_inv' y hy := by
    apply Subtype.ext
    ext i
    fin_cases i
    · simp [Real.exp_log (show 0 < y.1 0 from hy)]
    · simp
  open_source := isOpen_univ
  open_target := isOpen_lt continuous_const
    ((EuclideanSpace.proj (0 : Fin 2)).continuous.comp continuous_subtype_val)
  continuousOn_toFun := by
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 _).comp
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact Real.continuous_exp.comp (EuclideanSpace.proj (0 : Fin 2)).continuous
    · exact (EuclideanSpace.proj (1 : Fin 2)).continuous
  continuousOn_invFun := by
    apply ContinuousOn.comp (PiLp.continuous_toLp 2 _).continuousOn _ (mapsTo_univ _ _)
    refine continuousOn_pi.2 fun i => ?_
    fin_cases i
    · exact Real.continuousOn_log.comp
        ((EuclideanSpace.proj (0 : Fin 2)).continuous.comp continuous_subtype_val).continuousOn
        fun y hy => (show 0 < y.1 0 from hy).ne'
    · exact ((EuclideanSpace.proj (1 : Fin 2)).continuous.comp
        continuous_subtype_val).continuousOn

/-- The plane with its single half-plane chart. -/
@[implicit_reducible]
def planeHalfChartedSpace : ChartedSpace (EuclideanHalfSpace 2) Plane where
  atlas := {planeHalfChart}
  chartAt _ := planeHalfChart
  mem_chart_source x := mem_univ x
  chart_mem_atlas _ := mem_singleton _

variable (M : Type*) [TopologicalSpace M] [ChartedSpace Plane M]

/-- Half-plane charts on a surface charted on the plane. -/
@[implicit_reducible]
def halfPlaneChartedSpace : ChartedSpace (EuclideanHalfSpace 2) M :=
  letI := planeHalfChartedSpace
  ChartedSpace.comp (EuclideanHalfSpace 2) Plane M

/-- With these charts the surface is a topological manifold in the half-space model. -/
theorem halfPlane_isManifold_zero :
    letI := halfPlaneChartedSpace M
    IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 M := by
  let _ := halfPlaneChartedSpace M
  have h : HasGroupoid M (contDiffGroupoid 0 (modelWithCornersEuclideanHalfSpace 2)) := by
    rw [contDiffGroupoid_zero_eq]
    infer_instance
  exact { h with }

end R4Embedding
