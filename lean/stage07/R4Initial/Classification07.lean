import R4Embedding.ModelClassification
import R4Embedding.PolynomialSphere
import R4Initial.HalfSpaceCharts
import R4CoS.EvalStatement
import R4Initial.BoundaryNormalForm
import R4Initial.SmoothingReduction

/-! Stage 07 assembled from the topological classification of compact surfaces.
The remaining mathematics is isolated in four explicit statements: normal forms with
boundary and non-orientable normal forms are excluded, the orientable closed normal
forms are identified with the explicit models, and homeomorphisms onto the models are
smoothed. Together with the analytic statement they give the full target. No statement
here is asserted; every implication between them is proved. -/

noncomputable section
namespace R4Embedding

open Manifold R4CoS.Topology.ClassificationOfSurfaces
open scoped ContDiff
universe u

/-- A surface charted on the plane has no normal form with boundary components. -/
def NoBoundaryNormalFormStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace Plane M] (p n : ℕ), 1 ≤ n →
    IsEmpty (M ≃ₜ Quot (OrientableRel p n)) ∧ IsEmpty (M ≃ₜ Quot (NonOrientableRel p n))

/-- A smooth orientation excludes the closed non-orientable normal forms. -/
def NoNonOrientableNormalFormStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M],
    IsOrientableSurface M → ∀ p : ℕ, 1 ≤ p → IsEmpty (M ≃ₜ Quot (NonOrientableRel p 0))

/-- The closed orientable normal forms of positive genus are the explicit models. -/
def OrientableNormalFormModelStatement : Prop :=
  ∀ p : ℕ, 1 ≤ p → Nonempty (Quot (OrientableRel p 0) ≃ₜ PolynomialLevel p)

theorem polynomial_topological_classification_of_normal_forms
    (hbdry : NoBoundaryNormalFormStatement.{u})
    (hnon : NoNonOrientableNormalFormStatement.{u})
    (hmodel : OrientableNormalFormModelStatement) :
    PolynomialTopologicalClassificationStatement.{u} := by
  intro M _ _ _ _ _ _ horient
  let _ := halfPlaneChartedSpace M
  have := halfPlane_isManifold_zero M
  rcases classification_of_surfaces M with hS | ⟨p, n, ⟨hpn, ⟨hO⟩⟩ | ⟨hp, ⟨hN⟩⟩⟩
  · obtain ⟨e⟩ := hS
    exact ⟨0, ⟨e.trans polynomialZeroSphereHomeomorph.symm⟩⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · obtain ⟨e⟩ := hmodel p (hpn.resolve_right (by omega))
      exact ⟨p, ⟨hO.trans e⟩⟩
    · exact ((hbdry M p n hn).1.false hO).elim
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ((hnon M horient p hp).false hN).elim
    · exact ((hbdry M p n hn).2.false hN).elim

/-- The complete target from the five remaining statements. -/
theorem closed_statement_of_remaining_inputs
    (hbdry : NoBoundaryNormalFormStatement.{u})
    (hnon : NoNonOrientableNormalFormStatement.{u})
    (hmodel : OrientableNormalFormModelStatement)
    (hsmooth : PolynomialModelSmoothingStatement.{u})
    (hanalytic : IsometricEmbeddingFromThreeStatement.{u}) :
    ClosedOrientableSurfaceEmbeddingStatement.{u} :=
  closed_statement_of_polynomial_classification_and_analytic
    (polynomial_classification_of_topological_and_smoothing
      (polynomial_topological_classification_of_normal_forms hbdry hnon hmodel) hsmooth)
    hanalytic

/-- Normal forms with boundary are excluded (proved in `R4Initial.BoundaryNormalForm`). -/
theorem noBoundaryNormalFormStatement_holds : NoBoundaryNormalFormStatement.{u} :=
  fun M _ _ p n hn => isEmpty_homeomorph_normalForm_of_hole M p n hn

/-- The complete target from the four statements that remain open. -/
theorem closed_statement_of_four_inputs
    (hnon : NoNonOrientableNormalFormStatement.{u})
    (hmodel : OrientableNormalFormModelStatement)
    (hsmooth : PolynomialModelSmoothingStatement.{u})
    (hanalytic : IsometricEmbeddingFromThreeStatement.{u}) :
    ClosedOrientableSurfaceEmbeddingStatement.{u} :=
  closed_statement_of_remaining_inputs noBoundaryNormalFormStatement_holds hnon hmodel hsmooth
    hanalytic

/-- The complete target with smoothing reduced to its chart step. -/
theorem closed_statement_of_chartStep_inputs
    (hnon : NoNonOrientableNormalFormStatement.{u})
    (hmodel : OrientableNormalFormModelStatement)
    (hstep : ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace Plane M]
      [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] (g : ℕ),
      let _ := polynomialLevelChartedSpace g
      SmoothingChartStep M (PolynomialLevel g))
    (hanalytic : IsometricEmbeddingFromThreeStatement.{u}) :
    ClosedOrientableSurfaceEmbeddingStatement.{u} :=
  closed_statement_of_four_inputs hnon hmodel (polynomialModelSmoothing_of_chartStep hstep)
    hanalytic

end R4Embedding
