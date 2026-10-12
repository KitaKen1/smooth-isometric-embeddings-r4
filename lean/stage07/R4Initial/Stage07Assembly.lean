import R4Initial.ModelRealization
import R4Embedding.PolynomialOrientation

/-! Stage 07 assembly without the smoothing tools.

The polynomial levels are oriented (main-line `polynomialLevel_isOrientable`, ported to 4.35), so
stage 07d needs only the exclusion of the closed non-orientable normal forms. The complete target
then follows from three statements: that exclusion (in the universe of the surface and in universe
`0` for the models), the smoothing of homeomorphisms onto the models, and the analytic statement.
The first two are discharged by the chart step of `R4Initial.RelativeChartSmoothing`. -/

noncomputable section
namespace R4Embedding

universe u

/-- The polynomial levels are oriented smooth surfaces. -/
theorem polynomialLevelOrientableStatement_holds : PolynomialLevelOrientableStatement :=
  fun g => polynomialLevel_isOrientable g

/-- Stage 07d from the exclusion of the closed non-orientable normal forms alone. -/
theorem orientableNormalFormModelStatement_of_nonOrientable
    (hnon : NoNonOrientableNormalFormStatement.{0}) : OrientableNormalFormModelStatement :=
  orientableNormalFormModelStatement_of_exclusions hnon polynomialLevelOrientableStatement_holds

/-- The complete target from the non-orientable exclusion, the smoothing statement and the
analytic statement. -/
theorem closed_statement_of_exclusion_smoothing_analytic
    (hnon : NoNonOrientableNormalFormStatement.{u})
    (hnon₀ : NoNonOrientableNormalFormStatement.{0})
    (hsmooth : PolynomialModelSmoothingStatement.{u})
    (hanalytic : IsometricEmbeddingFromThreeStatement.{u}) :
    ClosedOrientableSurfaceEmbeddingStatement.{u} :=
  closed_statement_of_four_inputs hnon (orientableNormalFormModelStatement_of_nonOrientable hnon₀)
    hsmooth hanalytic

end R4Embedding
