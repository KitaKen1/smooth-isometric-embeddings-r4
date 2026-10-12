import R4Embedding.TransversePlane
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Construction of the fixed projection used in the coordinate argument.
The left inverse is built from an invertible testing map. On a surface, the
testing map consists of pairings with F_y and F_yy. -/

noncomputable section

namespace R4Embedding

section General

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Invert a nondegenerate testing map on the tangent image. -/
theorem exists_fixed_projection [FiniteDimensional ℝ E]
    (D : E →L[ℝ] V) (A : V →L[ℝ] E)
    (hinj : Function.Injective (A.comp D)) :
    ∃ L : V →L[ℝ] E, L.comp D = ContinuousLinearMap.id ℝ E ∧
      ∀ v, A v = 0 → L v = 0 := by
  have hsurj : Function.Surjective (A.comp D) :=
    LinearMap.surjective_of_injective (f := (A.comp D).toLinearMap) hinj
  let e : E ≃L[ℝ] E :=
    (LinearEquiv.ofBijective (A.comp D).toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  refine ⟨e.symm.toContinuousLinearMap.comp A, ?_, ?_⟩
  · ext x
    change e.symm (e x) = x
    exact e.symm_apply_apply x
  · intro v hv
    simp only [ContinuousLinearMap.comp_apply, hv, map_zero]

/-- The corresponding projection onto the transverse complement. -/
def complementProjection (D : E →L[ℝ] V) (L : V →L[ℝ] E) : V →L[ℝ] V :=
  ContinuousLinearMap.id ℝ V - D.comp L

theorem complementProjection_killed
    (D : E →L[ℝ] V) (L : V →L[ℝ] E)
    (hleft : L.comp D = ContinuousLinearMap.id ℝ E) :
    L.comp (complementProjection D L) = 0 := by
  ext v
  have h := congrArg (fun T : E →L[ℝ] E => T (L v)) hleft
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
  simp only [complementProjection, ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.id_apply, map_sub, h, sub_self, zero_apply]

theorem complementProjection_fixed_of_killed
    (D : E →L[ℝ] V) (L : V →L[ℝ] E) {v : V} (hv : L v = 0) :
    complementProjection D L v = v := by
  simp only [complementProjection, sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, hv, map_zero, sub_zero]

theorem complementProjection_idempotent
    (D : E →L[ℝ] V) (L : V →L[ℝ] E)
    (hleft : L.comp D = ContinuousLinearMap.id ℝ E) :
    (complementProjection D L).comp (complementProjection D L) = complementProjection D L := by
  ext v
  apply complementProjection_fixed_of_killed
  have h := congrArg (fun T : V →L[ℝ] E => T v) (complementProjection_killed D L hleft)
  exact h

end General

section Surface

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def surfaceTangentMap (u v : V) : (ℝ × ℝ) →L[ℝ] V :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight u +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight v

def surfaceTestingMap (v acc : V) : V →L[ℝ] (ℝ × ℝ) :=
  (innerSL ℝ v).prod (innerSL ℝ acc)

theorem surfaceTangentMap_apply (u v : V) (x : ℝ × ℝ) :
    surfaceTangentMap u v x = x.1 • u + x.2 • v := rfl

theorem surfaceTestingMap_apply (v acc w : V) :
    surfaceTestingMap v acc w = (inner ℝ v w, inner ℝ acc w) := by
  simp only [surfaceTestingMap, ContinuousLinearMap.prod_apply, innerSL_apply_apply]

/-- The nonzero Gauss coefficient makes the testing map nondegenerate on
the two-dimensional tangent image. -/
theorem surfaceTestingMap_tangent_injective
    {u v acc normal : V} {k l : ℝ}
    (hD : Function.Injective (surfaceTangentMap u v))
    (hacc : acc = k • u + l • v + normal) (hk : k ≠ 0)
    (hnu : inner ℝ u normal = 0) (hnv : inner ℝ v normal = 0) :
    Function.Injective ((surfaceTestingMap v acc).comp (surfaceTangentMap u v)) := by
  intro x y heq
  let w := surfaceTangentMap u v (x - y)
  have htest : surfaceTestingMap v acc w = 0 := by
    change surfaceTestingMap v acc (surfaceTangentMap u v (x - y)) = 0
    rw [map_sub, map_sub]
    exact sub_eq_zero.mpr heq
  have hwv : inner ℝ w v = 0 := by
    have h := congrArg Prod.fst htest
    simpa only [surfaceTestingMap_apply, Prod.fst_zero, real_inner_comm v w] using h
  have hwacc : inner ℝ w acc = 0 := by
    have h := congrArg Prod.snd htest
    simpa only [surfaceTestingMap_apply, Prod.snd_zero, real_inner_comm acc w] using h
  have hw : w = 0 := transverse_orthogonal_intersection hacc hk hnu hnv
    (surfaceTangentMap_apply u v (x - y)) hwv hwacc
  have hxy : x - y = 0 := hD (by simpa only [map_zero] using hw)
  exact sub_eq_zero.mp hxy

/-- A genuine fixed projection onto surface coordinates exists and kills the
oscillation plane. No projection is assumed as an input to this theorem. -/
theorem exists_surface_fixed_projection
    {u v acc normal : V} {k l : ℝ}
    (hD : Function.Injective (surfaceTangentMap u v))
    (hacc : acc = k • u + l • v + normal) (hk : k ≠ 0)
    (hnu : inner ℝ u normal = 0) (hnv : inner ℝ v normal = 0) :
    ∃ L : V →L[ℝ] (ℝ × ℝ),
      L.comp (surfaceTangentMap u v) = ContinuousLinearMap.id ℝ (ℝ × ℝ) ∧
      ∀ w, inner ℝ w v = 0 → inner ℝ w acc = 0 → L w = 0 := by
  obtain ⟨L, hleft, hkill⟩ := exists_fixed_projection (surfaceTangentMap u v)
    (surfaceTestingMap v acc) (surfaceTestingMap_tangent_injective hD hacc hk hnu hnv)
  refine ⟨L, hleft, ?_⟩
  intro w hwv hwacc
  apply hkill
  apply Prod.ext
  · change inner ℝ v w = 0
    exact (real_inner_comm w v).trans hwv
  · change inner ℝ acc w = 0
    exact (real_inner_comm w acc).trans hwacc

end Surface
end R4Embedding
