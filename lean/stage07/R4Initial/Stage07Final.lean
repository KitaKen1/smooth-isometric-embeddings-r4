import R4Initial.Stage07Assembly
import R4Initial.RelativeChartSmoothing
import R4Initial.NonOrientableExclusion

/-! Stage 07 closed: the chart step of `R4Initial.RelativeChartSmoothing` gives the exclusion of
the closed non-orientable normal forms and the smoothing of homeomorphisms onto the polynomial
models; with the genus identification of stage 07d, the complete target follows from the analytic
statement alone. -/

noncomputable section
namespace R4Embedding

universe u

/-- The closed non-orientable normal forms are excluded for smooth oriented surfaces. -/
theorem noNonOrientableNormalFormStatement_holds : NoNonOrientableNormalFormStatement.{u} :=
  noNonOrientableNormalFormStatement_of_chartStep fun _ _ _ _ _ _ => smoothingChartStep_holds

/-- The closed orientable normal forms are the polynomial models of the same genus. -/
theorem orientableNormalFormModelStatement_holds : OrientableNormalFormModelStatement :=
  orientableNormalFormModelStatement_of_nonOrientable noNonOrientableNormalFormStatement_holds.{0}

/-- Every closed connected orientable smooth surface is homeomorphic to an explicit model. -/
theorem polynomialTopologicalClassificationStatement_holds :
    PolynomialTopologicalClassificationStatement.{u} :=
  polynomial_topological_classification_of_normal_forms noBoundaryNormalFormStatement_holds
    noNonOrientableNormalFormStatement_holds orientableNormalFormModelStatement_holds

/-- Every closed connected orientable smooth surface is diffeomorphic, in its own atlas, to an
explicit model. -/
theorem polynomialModelClassificationStatement_holds :
    PolynomialModelClassificationStatement.{u} :=
  polynomial_classification_of_topological_and_smoothing
    polynomialTopologicalClassificationStatement_holds polynomialModelSmoothingStatement_holds

/-- Every closed connected orientable smooth surface, in its own atlas, has a smooth embedding in
`ℝ³` with injective differential. -/
theorem connectedInitialThreeEmbeddingStatement_holds :
    ConnectedInitialThreeEmbeddingStatement.{u} :=
  connected_initial_of_polynomial_classification polynomialModelClassificationStatement_holds

/-- Every closed orientable smooth surface, in its own atlas (empty and disconnected surfaces
included), has a smooth embedding in `ℝ³` with injective differential. -/
theorem initialThreeEmbeddingStatement_holds : InitialThreeEmbeddingStatement.{u} :=
  initial_three_statement_of_connected_statement connectedInitialThreeEmbeddingStatement_holds

open scoped ContDiff in
/-- Every closed orientable smooth surface, in its own atlas, has a smooth embedding in the unit
sphere of `ℝ⁴` with injective differential. -/
theorem exists_initial_spherical_embedding (M : Type u) [TopologicalSpace M]
    [ChartedSpace Plane M] [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
    (horient : IsOrientableSurface M) :
    ∃ I : M → Space, ContMDiff planeModel spaceModel ∞ I ∧ (∀ p, ‖I p‖ = 1) ∧
      (∀ p, Function.Injective (mfderiv planeModel spaceModel I p)) ∧ Function.Injective I := by
  obtain ⟨f, hf, hfinj, himm⟩ := initialThreeEmbeddingStatement_holds M horient
  exact exists_spherical_embedding_of_three_embedding hf hfinj himm

/-- The complete target from the three statements that remain open. -/
theorem closed_statement_of_three_inputs
    (hnon : NoNonOrientableNormalFormStatement.{u})
    (hmodel : OrientableNormalFormModelStatement)
    (hanalytic : IsometricEmbeddingFromThreeStatement.{u}) :
    ClosedOrientableSurfaceEmbeddingStatement.{u} :=
  closed_statement_of_four_inputs hnon hmodel polynomialModelSmoothingStatement_holds hanalytic

/-- The complete target from the analytic statement alone. -/
theorem closed_statement_of_analytic (hanalytic : IsometricEmbeddingFromThreeStatement.{u}) :
    ClosedOrientableSurfaceEmbeddingStatement.{u} :=
  closed_statement_of_three_inputs noNonOrientableNormalFormStatement_holds
    orientableNormalFormModelStatement_holds hanalytic

end R4Embedding
