import R4Embedding.SphericalTransfer
import R4Analytic.AnalyticSphericalEmbedding

/-! Reduce the remaining initial spherical embedding input to an actual
smooth embedding in Euclidean three-space. This conditional analytic entry
is written but has not yet been compiled or axioms-audited. -/

noncomputable section
namespace R4Embedding

open Manifold
open scoped ContDiff

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem analytic_isometric_embedding_of_three_embedding (g : SmoothMetric M)
    {f : M → ThreeSpace} (hf : ContMDiff planeModel threeModel ∞ f)
    (hfinj : Function.Injective f)
    (himm : ∀ p, Function.Injective (mfderiv planeModel threeModel f p)) :
    ∃ W : M → Space, IsSmoothIsometricEmbedding g W := by
  obtain ⟨I,hI,hunit,hImm,hIinj⟩ := exists_spherical_embedding_of_three_embedding hf hfinj himm
  exact analytic_isometric_embedding_of_spherical_embedding g hI hunit hImm hIinj

end R4Embedding
