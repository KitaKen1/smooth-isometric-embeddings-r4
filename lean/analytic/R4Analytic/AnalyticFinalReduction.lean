import R4Embedding.MainStatement
import R4Analytic.AnalyticThreeEmbedding

/-! Connect the analytic construction to the complete quantified target.
The analytic dependency chain has not yet been compiled and audited here.
The connected initial-embedding theorem remains an explicit input. -/

noncomputable section
namespace R4Embedding

open Manifold
open scoped ContDiff
universe u

theorem analytic_isometric_embedding_from_three_statement :
    IsometricEmbeddingFromThreeStatement.{u} := by
  intro M _ _ _ _ _ g f hs hi hm
  exact analytic_isometric_embedding_of_three_embedding g hs hi hm

theorem analytic_closed_statement_of_connected_initial
    (hinitial : ConnectedInitialThreeEmbeddingStatement.{u}) :
    ClosedOrientableSurfaceEmbeddingStatement.{u} :=
  closed_statement_of_connected_initial_and_analytic hinitial
    analytic_isometric_embedding_from_three_statement

end R4Embedding
