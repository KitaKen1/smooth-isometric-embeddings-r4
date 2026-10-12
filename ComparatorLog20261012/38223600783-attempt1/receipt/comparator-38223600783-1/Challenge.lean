import FCTargetDefinitions

namespace SmoothIsometricEmbeddingR4

open scoped ContDiff Manifold


/-- Does every closed orientable smooth surface with any smooth Riemannian metric
admit a smooth isometric embedding into four-space? The answer is affirmative [Ki26]. -/
theorem smooth_isometric_embedding_R4 :
    True ↔
      ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
        [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ M] [CompactSpace M] [T2Space M],
        IsOrientableSurface M →
          ∀ g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
              (EuclideanSpace ℝ (Fin 2))
              (fun p : M => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p),
            ∃ F : M → EuclideanSpace ℝ (Fin 4),
              ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
                  𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ∞ F ∧ Function.Injective F ∧
                ∀ (p : M) (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p),
                  let df := (NormedSpace.fromTangentSpace (F p)).toContinuousLinearMap.comp
                    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) F p)
                  inner ℝ (df v) (df w) = g.inner p v w := by
  sorry

end SmoothIsometricEmbeddingR4
