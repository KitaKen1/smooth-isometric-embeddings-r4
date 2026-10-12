import R4Analytic.AnalyticCircularFamilyStep
import OAI.Geometry.SurfaceImmersion.Primitive.CircularMetricSequence

/-! Use the actual ordered metrics and restrict the remaining boundary curves
at every stage. Injectivity belongs to the same metric-preserving output.
Pending compilation and transitive axiom audit. -/

noncomputable section
namespace R4Embedding
open OAI.ClosedSurfaceR4 OAI.ClosedSurfaceR4.FiniteOrderSmoothing
open OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily
open Set Manifold
open scoped ContDiff Topology
open SurfaceJetCoordinates SmallModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
variable {B : SmoothingAtlas M}
theorem analytic_circular_sequence_embeddings (N : ℕ) :
    ∀ (d : CircularPrimitiveFamily B (Fin N)) (g : Fin (N+1) → SmoothMetric M),
    (∀ a : Fin N, (g a.succ).inner = (g a.castSucc).inner +
      (fun p => (d.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d.phase a) p)) →
    (∀ a : Fin N, d.ConvexMetric (g a.castSucc) a) →
    ∀ (F : M → Space) (n : PreferredNormal F),
    IsSmoothIsometricEmbedding (g 0) F → MetricGoodPhaseData (g 0) F →
    FiniteBoundaryGeometry d.curves (boundaryCrossingSet d.curves univ) F n →
    ∃ W : M → Space, IsSmoothIsometricEmbedding (g (Fin.last N)) W ∧
      Nonempty (MetricGoodPhaseData (g (Fin.last N)) W) ∧ Nonempty (PreferredNormal W) := by
  classical
  induction N with
  | zero =>
    intro d g _ _ F n hF data _
    exact ⟨F,hF,⟨data⟩,⟨n⟩⟩
  | succ N ih =>
    intro d g hstep hconvex F n hF data hgeom
    obtain ⟨W,hW,⟨good⟩,_hposition,normal,hnew⟩ :=
      analytic_circular_family_embedding_step d 0
        (analytic_isometry_iff_local_spec.mpr hF.1) hF.2 n hgeom (hconvex 0) data
        (g (Fin.succ 0)) (hstep 0) 1 (by norm_num)
    let d' := d.restrict (Fin.succ : Fin N → Fin (N+1)) (Fin.succ_injective N)
    let g' : Fin (N+1) → SmoothMetric M := fun a => g a.succ
    have hstep' (a : Fin N) : (g' a.succ).inner = (g' a.castSucc).inner +
        (fun p => (d'.amplitude a p)^2 • SmoothingAtlas.phaseDifferentialSquare (d'.phase a) p) := by
      simpa only [g',d',OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily.restrict,
        Function.comp_apply,ConvexMetric,Fin.succ_castSucc] using hstep a.succ
    have hconvex' (a : Fin N) : d'.ConvexMetric (g' a.castSucc) a := by
      simpa only [g',d',OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CircularPrimitiveFamily.restrict,
        Function.comp_apply,ConvexMetric,Fin.succ_castSucc] using hconvex a.succ
    let f : Fin N → {j : Fin (N+1) // j ≠ 0} := fun a => ⟨a.succ,Fin.succ_ne_zero a⟩
    have hf : Function.Injective f := by
      intro a b hab
      exact Fin.succ_injective N (congrArg Subtype.val hab)
    have hsub : boundaryCrossingSet d'.curves univ ⊆
        boundaryCrossingSet (fun j : {j : Fin (N+1) // j ≠ 0} => d.curves j) univ := by
      rintro p ⟨a,_,b,_,hab,ha,hb⟩
      exact ⟨f a,mem_univ _,f b,mem_univ _,fun h => hab (hf h),ha,hb⟩
    have hgeom' : FiniteBoundaryGeometry d'.curves (boundaryCrossingSet d'.curves univ) W normal :=
      hnew.restrict f hf hsub
    obtain ⟨V,hV,hgood,hN⟩ := ih d' g' hstep' hconvex' W normal hW good hgeom'
    exact ⟨V,hV,hgood,hN⟩

end R4Embedding
