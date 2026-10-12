import R4Initial.PresentationEuler
import R4Initial.Classification07
import R4CoS.FiniteCyclicCanonicalRealization
import R4CoS.FiniteCyclicTerminalNormalization

/-! Stage 07d(C): the Euler characteristic pins the normal form of the polynomial model.

Given a polygonal presentation of `PolynomialLevel g` with `χ = 2 − 2g` and `g ≥ 1`, the normal
form reached by Lean Pool's normalization is `orientable g 0`:

* the sphere has `χ = 2`;
* normal forms with boundary components are excluded by `NoBoundaryNormalFormStatement`;
* the closed non-orientable normal forms are excluded by `NoNonOrientableNormalFormStatement`,
  since the polynomial level is a smooth oriented surface;
* `χ (orientable p 0) = 2 − 2p`, so `p = g`.

The presentation itself (stage 07d(B)) is a hypothesis here. -/

noncomputable section
namespace R4Embedding

open Manifold R4CoS.Topology.ClassificationOfSurfaces
open scoped ContDiff

/-- A polygonal presentation of the polynomial model of genus `g` with the expected Euler
characteristic. -/
structure PolynomialPresentation (g : ℕ) where
  presentation : FiniteCyclicPresentation
  valid : presentation.IsSurfaceValid
  connected : presentation.IsConnected
  euler : eulerChar presentation = 2 - 2 * g
  realization : Nonempty (presentation.PolygonalRealization valid ≃ₜ PolynomialLevel g)

/-- The polynomial levels are oriented smooth surfaces (main-line
`R4Embedding.polynomialLevel_isOrientable`, to be ported). -/
def PolynomialLevelOrientableStatement : Prop :=
  ∀ g : ℕ,
    let _ := polynomialLevelChartedSpace g
    let _ := polynomialLevel_isManifold g
    IsOrientableSurface (PolynomialLevel g)

/-- A canonical presentation homeomorphic to the polynomial model of genus `g ≥ 1` whose Euler
characteristic is `2 − 2g` is the closed orientable normal form of genus `g`. -/
theorem orientable_of_canonical_euler {g : ℕ} (hg : 1 ≤ g)
    (hbdry : NoBoundaryNormalFormStatement.{0})
    (hnon : NoNonOrientableNormalFormStatement.{0})
    (horient : PolynomialLevelOrientableStatement)
    (N : NormalForm) (hN : N.IsEvalAdmissible)
    (hχ : eulerChar N.canonicalPresentation = 2 - 2 * g)
    (e : PolynomialLevel g ≃ₜ
      N.canonicalPresentation.PolygonalRealization (N.canonicalPresentation_isSurfaceValid hN)) :
    Nonempty (Quot (OrientableRel g 0) ≃ₜ PolynomialLevel g) := by
  letI := polynomialLevelChartedSpace g
  haveI : IsManifold planeModel ∞ (PolynomialLevel g) := polynomialLevel_isManifold g
  cases N with
  | sphere =>
    exfalso
    have h2 : eulerChar NormalForm.sphere.canonicalPresentation = 2 :=
      eulerChar_twoMonogonSphere
    rw [h2] at hχ
    omega
  | orientable p n =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hp : 1 ≤ p := by
        rcases hN with h | h
        · exact h
        · omega
      rw [eulerChar_canonical_orientable hp] at hχ
      have hpg : p = g := by omega
      subst hpg
      exact ⟨(e.trans (NormalForm.canonicalOrientableRealizationHomeomorph hN)).symm⟩
    · exact ((hbdry (PolynomialLevel g) p n (by omega)).1.false
        (e.trans (NormalForm.canonicalOrientableRealizationHomeomorph hN))).elim
  | nonOrientable p n =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ((hnon (PolynomialLevel g) (horient g) p hN).false
        (e.trans (NormalForm.canonicalNonOrientableRealizationHomeomorph hN))).elim
    · exact ((hbdry (PolynomialLevel g) p n (by omega)).2.false
        (e.trans (NormalForm.canonicalNonOrientableRealizationHomeomorph hN))).elim

/-- Stage 07d from its geometric input: polygonal presentations of the polynomial models with
the expected Euler characteristic identify every closed orientable normal form with the model
of the same genus. -/
theorem orientableNormalFormModelStatement_of_presentations
    (hbdry : NoBoundaryNormalFormStatement.{0})
    (hnon : NoNonOrientableNormalFormStatement.{0})
    (horient : PolynomialLevelOrientableStatement)
    (hP : ∀ g : ℕ, 1 ≤ g → Nonempty (PolynomialPresentation g)) :
    OrientableNormalFormModelStatement := by
  intro g hg
  obtain ⟨P⟩ := hP g hg
  obtain ⟨eP⟩ := P.realization
  let R := FiniteCyclicPresentation.normalizeConnectedToCanonical
    ⟨P.presentation, P.valid⟩ P.connected
  obtain ⟨eR⟩ := R.polygonallyEquivalent
  refine orientable_of_canonical_euler hg hbdry hnon horient R.normalForm R.admissible ?_
    (eP.symm.trans eR)
  rw [← P.euler]
  exact (eulerChar_normalizationEquivalent R.equivalent).symm

end R4Embedding
