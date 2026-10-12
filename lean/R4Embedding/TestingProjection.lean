import R4Embedding.FixedProjection
import R4Embedding.LocalOscillation
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The transverse direction can be encoded as the kernel of a testing map.
Inverting the testing map on the tangent image constructs a local continuous
complement. Thus no global transverse bundle or tubular neighbourhood is needed
for the local injectivity argument. -/

noncomputable section

namespace R4Embedding

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def testingLeftProjection (D : E →L[ℝ] V) (A : V →L[ℝ] E) : V →L[ℝ] E :=
  (A.comp D).inverse.comp A

def testingComplementProjection (D : E →L[ℝ] V) (A : V →L[ℝ] E) : V →L[ℝ] V :=
  complementProjection D (testingLeftProjection D A)

theorem testing_comp_isInvertible [FiniteDimensional ℝ E]
    (D : E →L[ℝ] V) (A : V →L[ℝ] E)
    (hinj : Function.Injective (A.comp D)) : (A.comp D).IsInvertible := by
  have hsurj := LinearMap.surjective_of_injective (f := (A.comp D).toLinearMap) hinj
  exact ⟨(LinearEquiv.ofBijective (A.comp D).toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv,
    rfl⟩

theorem testingLeftProjection_left
    (D : E →L[ℝ] V) (A : V →L[ℝ] E) (hinv : (A.comp D).IsInvertible) :
    (testingLeftProjection D A).comp D = ContinuousLinearMap.id ℝ E := by
  simpa only [testingLeftProjection, ContinuousLinearMap.comp_assoc] using hinv.inverse_comp_self

theorem testingLeftProjection_kills
    (D : E →L[ℝ] V) (A : V →L[ℝ] E) (W : E →L[ℝ] V) (hW : A.comp W = 0) :
    (testingLeftProjection D A).comp W = 0 := by
  ext x
  have hx := congrArg (fun T : E →L[ℝ] E => T x) hW
  simp only [ContinuousLinearMap.comp_apply, zero_apply] at hx
  simp only [testingLeftProjection, ContinuousLinearMap.comp_apply, hx, map_zero, zero_apply]

theorem testingComplementProjection_fixes
    (D : E →L[ℝ] V) (A : V →L[ℝ] E) (W : E →L[ℝ] V) (hW : A.comp W = 0) :
    (testingComplementProjection D A).comp W = W := by
  ext x
  apply complementProjection_fixed_of_killed
  have hx := congrArg (fun T : E →L[ℝ] E => T x) (testingLeftProjection_kills D A W hW)
  exact hx

/-- Only invertibility at the centre is needed for continuity of the chosen
complement there. No invertibility claim is made away from the centre. -/
theorem testingComplementProjection_continuousAt [CompleteSpace E]
    (D : E → E →L[ℝ] V) (A : E → V →L[ℝ] E) (p : E)
    (hD : ContinuousAt D p) (hA : ContinuousAt A p)
    (hinv : ((A p).comp (D p)).IsInvertible) :
    ContinuousAt (fun q => testingComplementProjection (D q) (A q)) p := by
  have hAD : ContinuousAt (fun q => (A q).comp (D q)) p := hA.clm_comp hD
  have hi : ContinuousAt (fun q => ((A q).comp (D q)).inverse) p :=
    (hinv.contDiffAt_map_inverse (n := 0)).continuousAt.comp_of_eq hAD rfl
  have hL : ContinuousAt (fun q => testingLeftProjection (D q) (A q)) p := hi.clm_comp hA
  exact continuousAt_const.sub (hD.clm_comp hL)

/-- Local embedding preservation with no assumed projection: transversality
is expressed directly by the testing map, and all geometric operators are
constructed from A and D. -/
theorem exists_injective_ball_of_testing_transversality [FiniteDimensional ℝ E]
    (D : E → E →L[ℝ] V) (A : E → V →L[ℝ] E) (p : E)
    (hD : ContinuousAt D p) (hA : ContinuousAt A p)
    (hinj : Function.Injective ((A p).comp (D p))) {B : ℝ} (hB : 0 ≤ B) :
    ∃ r ρ : ℝ, 0 < r ∧ 0 < ρ ∧
      ∀ (f : E → V) (df W : E → E →L[ℝ] V),
        (∀ q ∈ Metric.ball p r, HasFDerivWithinAt f (df q) (Metric.ball p r) q) →
        (∀ q ∈ Metric.ball p r, (A q).comp (W q) = 0) →
        (∀ q ∈ Metric.ball p r, ‖W q‖ ≤ B) →
        (∀ q ∈ Metric.ball p r, ‖df q - D q - W q‖ ≤ ρ) →
        Set.InjOn f (Metric.ball p r) := by
  have hinv := testing_comp_isInvertible (D p) (A p) hinj
  have hleft := testingLeftProjection_left (D p) (A p) hinv
  have hP := testingComplementProjection_continuousAt D A p hD hA hinv
  have hkill : (testingLeftProjection (D p) (A p)).comp
      (testingComplementProjection (D p) (A p)) = 0 :=
    complementProjection_killed _ _ hleft
  obtain ⟨r, ρ, hr, hρ, hall⟩ := exists_injective_ball_of_transverse_perturbation D
    (fun q => testingComplementProjection (D q) (A q))
    (testingLeftProjection (D p) (A p)) p hD hP hleft hkill hB
  refine ⟨r, ρ, hr, hρ, ?_⟩
  intro f df W hf hW hbound hresidual
  exact hall f df W hf
    (fun q hq => testingComplementProjection_fixes (D q) (A q) (W q) (hW q hq))
    hbound hresidual

end R4Embedding
