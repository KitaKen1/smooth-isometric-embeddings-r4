import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith

/-!
# Quantitative injectivity in a fixed coordinate chart

The derivative of a projected oscillatory map is close to the identity.
The mean value inequality then gives a lower bound for point separation.
This is the local part of embedding preservation, with no tubular map.
-/

namespace R4Embedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A map whose derivative is within `c < 1` of the identity separates points
on a convex coordinate set. -/
theorem norm_sub_le_of_derivative_close_id
    {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E} {c : ℝ}
    (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hclose : ∀ x ∈ s, ‖f' x - ContinuousLinearMap.id ℝ E‖ ≤ c)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    (1 - c) * ‖y - x‖ ≤ ‖f y - f x‖ := by
  have herror := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le' hf hclose hx hy
  have htriangle : ‖y - x‖ ≤ ‖f y - f x‖ + ‖f y - f x - (y - x)‖ := by
    calc
      ‖y - x‖ = ‖(f y - f x) - (f y - f x - (y - x))‖ := by
        congr 1
        abel
      _ ≤ ‖f y - f x‖ + ‖f y - f x - (y - x)‖ := norm_sub_le _ _
  simp only [ContinuousLinearMap.id_apply] at herror
  nlinarith

/-- The quantitative lower bound proves injectivity without controlling
second or higher derivatives of the oscillatory map. -/
theorem injOn_of_derivative_close_id
    {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E} {c : ℝ}
    (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hclose : ∀ x ∈ s, ‖f' x - ContinuousLinearMap.id ℝ E‖ ≤ c)
    (hc : c < 1) : Set.InjOn f s := by
  intro x hx y hy hxy
  have h := norm_sub_le_of_derivative_close_id hs hf hclose hx hy
  rw [hxy, sub_self, norm_zero] at h
  have hnorm : ‖y - x‖ = 0 := by
    nlinarith [norm_nonneg (y - x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm

end R4Embedding
