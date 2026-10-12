import R4Embedding.LocalInjectivity
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-! Fixed projections eliminate the large transverse term. Only the projected
derivative, rather than the full derivative, must be close to the identity. -/

namespace R4Embedding

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A fixed projection supplies a quantitative separation estimate. -/
theorem norm_sub_le_of_projected_derivative_close_id
    {s : Set E} {f : E → V} {df : E → E →L[ℝ] V} {c : ℝ}
    (L : V →L[ℝ] E) (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (df x) s x)
    (hclose : ∀ x ∈ s, ‖L.comp (df x) - ContinuousLinearMap.id ℝ E‖ ≤ c)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    (1 - c) * ‖y - x‖ ≤ ‖L‖ * ‖f y - f x‖ := by
  have h := norm_sub_le_of_derivative_close_id hs
    (fun x hx => L.hasFDerivAt.comp_hasFDerivWithinAt x (hf x hx)) hclose hx hy
  exact h.trans (by simpa only [Function.comp_apply, L.map_sub] using (L.le_opNorm (f y - f x)))

/-- Injectivity follows even if the unprojected derivative oscillates by an
order-one amount. -/
theorem injOn_of_projected_derivative_close_id
    {s : Set E} {f : E → V} {df : E → E →L[ℝ] V} {c : ℝ}
    (L : V →L[ℝ] E) (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (df x) s x)
    (hclose : ∀ x ∈ s, ‖L.comp (df x) - ContinuousLinearMap.id ℝ E‖ ≤ c)
    (hc : c < 1) : Set.InjOn f s := by
  have hi := injOn_of_derivative_close_id hs
    (fun x hx => L.hasFDerivAt.comp_hasFDerivWithinAt x (hf x hx)) hclose hc
  intro x hx y hy hxy
  exact hi hx hy (congrArg L hxy)

/-- Three independently controlled pieces give the derivative budget. The
transverse term is allowed to be large before projection. -/
theorem projected_derivative_budget
    (L : V →L[ℝ] E) (df old transverse residual : E →L[ℝ] V)
    {a b c : ℝ} (hdecomp : df = old + transverse + residual)
    (hold : ‖L.comp old - ContinuousLinearMap.id ℝ E‖ ≤ a)
    (htransverse : ‖L.comp transverse‖ ≤ b)
    (hresidual : ‖L.comp residual‖ ≤ c) :
    ‖L.comp df - ContinuousLinearMap.id ℝ E‖ ≤ a + b + c := by
  have heq : L.comp df - ContinuousLinearMap.id ℝ E =
      (L.comp old - ContinuousLinearMap.id ℝ E) + L.comp transverse + L.comp residual := by
    ext v
    simp only [hdecomp, ContinuousLinearMap.comp_apply, add_apply, sub_apply, map_add]
    abel
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add hold htransverse)) hresidual)

/-- A fixed projection kills the complement at the centre of a patch.
Variation of the complement controls the projected transverse term elsewhere.
The equation `P.comp W = W` expresses that the range of W lies in that plane. -/
theorem projected_transverse_bound
    (L : V →L[ℝ] E) (P P₀ : V →L[ℝ] V) (W : E →L[ℝ] V)
    (hrange : P.comp W = W) (hkill : L.comp P₀ = 0) :
    ‖L.comp W‖ ≤ ‖L‖ * ‖P - P₀‖ * ‖W‖ := by
  have heq : L.comp W = (L.comp (P - P₀)).comp W := by
    ext v
    have hW := congrArg (fun A : E →L[ℝ] V => A v) hrange
    have hzero := congrArg (fun A : V →L[ℝ] E => A (W v)) hkill
    simp only [ContinuousLinearMap.comp_apply, zero_apply] at hW hzero
    simp only [ContinuousLinearMap.comp_apply, sub_apply, map_sub, hW, hzero, sub_zero]
  rw [heq]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg W))

/-- Uniform boundedness of the transverse term can be used as an explicit
error budget once the complement varies by at most η on the patch. -/
theorem projected_transverse_bound_of_bounds
    (L : V →L[ℝ] E) (P P₀ : V →L[ℝ] V) (W : E →L[ℝ] V)
    (hrange : P.comp W = W) (hkill : L.comp P₀ = 0)
    {η B : ℝ} (hP : ‖P - P₀‖ ≤ η) (hW : ‖W‖ ≤ B) :
    ‖L.comp W‖ ≤ ‖L‖ * η * B := by
  have hη : 0 ≤ η := (norm_nonneg (P - P₀)).trans hP
  exact (projected_transverse_bound L P P₀ W hrange hkill).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hP (norm_nonneg L)) hW
      (norm_nonneg W) (mul_nonneg (norm_nonneg L) hη))

/-- Convenient strict budget for a single coordinate patch. -/
theorem injOn_of_projected_derivative_decomposition
    {s : Set E} {f : E → V} {df old transverse residual : E → E →L[ℝ] V}
    (L : V →L[ℝ] E) {a b c : ℝ} (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (df x) s x)
    (hdecomp : ∀ x ∈ s, df x = old x + transverse x + residual x)
    (hold : ∀ x ∈ s, ‖L.comp (old x) - ContinuousLinearMap.id ℝ E‖ ≤ a)
    (htransverse : ∀ x ∈ s, ‖L.comp (transverse x)‖ ≤ b)
    (hresidual : ∀ x ∈ s, ‖L.comp (residual x)‖ ≤ c)
    (hbudget : a + b + c < 1) : Set.InjOn f s := by
  apply injOn_of_projected_derivative_close_id L hs hf _ hbudget
  intro x hx
  exact projected_derivative_budget L _ _ _ _ (hdecomp x hx)
    (hold x hx) (htransverse x hx) (hresidual x hx)

end R4Embedding
