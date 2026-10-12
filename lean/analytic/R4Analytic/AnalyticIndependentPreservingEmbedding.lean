import R4Analytic.AnalyticIndependentPreservingProfiles
import R4Analytic.AnalyticPrimitiveAtlas
import OAI.Geometry.SurfaceImmersion.Primitive.ConstructedCircularPrimitive
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseGaussRepresentative
import OAI.Geometry.SurfaceImmersion.Primitive.AnalyticCurveCrossingLoop
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseMetricPositive
import OAI.Geometry.SurfaceImmersion.Primitive.ExactCircularPrimitive
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseMetricRegularity
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseMetricRead
import OAI.Geometry.SurfaceImmersion.Primitive.PhaseCircularPeriod
import OAI.Geometry.SurfaceImmersion.Primitive.ExactPhaseOriginalProfiles
import OAI.Geometry.SurfaceImmersion.Primitive.PhaseLeadingProfileStability
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveProfileStability
import OAI.Geometry.SurfaceImmersion.Geometry.ExactGeometricFastFamily
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveMetric
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasMetricJetMargins

/-! Use the actual independent phase-atlas construction with A₀ distinct from
data.A. Retain all conclusions on the same W.
Pending compilation and transitive axiom audit. -/

namespace R4Embedding

open OAI.ClosedSurfaceR4 OAI.ClosedSurfaceR4.FiniteOrderSmoothing

/-! Apply the actual preserving primitive construction at tolerances chosen
before its output. The resulting single W is both isometric and injective,
and retains the phase data and boundary conditions needed for the next step.
This is a prepared single-step theorem; it does not construct the initial
embedding or the finite primitive decomposition of an arbitrary metric. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector GeometryPreservation
local instance retainedIndependent_preservingEmbeddingBoundaryFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance retainedIndependent_preservingEmbeddingBoundaryFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance retainedIndependent_preservingEmbeddingBoundaryDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance retainedIndependent_preservingEmbeddingBoundaryDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance retainedIndependent_preservingEmbeddingBoundarySectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance retainedIndependent_preservingEmbeddingBoundarySectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
open SurfaceJetCoordinates SurfaceVelocityFamily VelocityFrame
variable {g : SmoothMetric M} {F : M → Space}

theorem analytic_independent_preserving_circular_primitive_embedding [T2Space M] (data : MetricGoodPhaseData g F) (A₀ : SmoothingAtlas M)
    (houter : ∀ i x, x ∈ tsupport (A₀.weight i) → A₀.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
    (hOld : IsSmoothIsometricMap g F) (hFinj : Function.Injective F)
    (i : A₀.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
    (hcover : (A₀.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source)
    {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    {n : SmallModes.Base → NormalFrame.Vec} {T U : Set SmallModes.Base}
    (hT : IsCompact T) (hU : IsOpen U) (hTU : T ⊆ U)
    (hn : ContDiffOn ℝ ∞ n U)
    (hI : ∀ p ∈ U, Function.Injective (fderiv ℝ (A₀.phaseRealChartMap i e.symm F) p))
    (hN : ∀ p ∈ U, SmallModes.coordDeriv SmallModes.dx (A₀.phaseRealChartMap i e.symm F) p ⬝ᵥ n p = 0 ∧
      SmallModes.coordDeriv SmallModes.dy (A₀.phaseRealChartMap i e.symm F) p ⬝ᵥ n p = 0 ∧ n p ⬝ᵥ n p = 1)
    (hHess : ∀ p ∈ U, 0 < PhaseGeometry.coordinateMetricHessian
      (RealModes.inducedCoordinateMetric (A₀.phaseRealChartMap i e.symm F)) Prod.fst p SmallModes.dy SmallModes.dy)
    (haT : ∀ p ∈ T, 0 ≤ a p)
    (hboundary : ∀ p ∈ T, a p = 0 →
      realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy p ≠ 0 ∧
      normalize (realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy p) ≠ -n p)
    {ι : Type*} [Finite ι] {Curves : ι → Set SmallModes.Base}
    (hCurves : ∀ j, IsCompact (Curves j)) (hCurvesT : ∀ j, Curves j ⊆ T)
    {P : Set SmallModes.Base} (hP : P.Finite)
    (hlocal : ∀ p ∈ (⋃ j, Curves j) \ P, ∃ N : Set SmallModes.Base, IsOpen N ∧ p ∈ N ∧
      ∃ f : SmallModes.Base → ℝ, ContDiffOn ℝ ∞ f N ∧
        (∀ x ∈ (⋃ j, Curves j) ∩ N, f x = 0) ∧ fderiv ℝ f p (0,1) ≠ 0)
    {E : Set SmallModes.Base} (hE : E.Finite) (hET : E ⊆ T) (haE : ∀ x ∈ E, 0 < a x)
    (slopeBound : ℝ) (hSlope : 0 ≤ slopeBound)
    {b c : ι → SmallModes.Base → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) (hc : ∀ j, ContDiff ℝ ∞ (c j))
    (hbc : ∀ j, ∀ x ∈ Curves j, b j x ≠ 0 ∨ c j x ≠ 0)
    (S : TopologicalSpace.Opens JetPolynomial.Base)
    (hSc : IsCompact (closure (S : Set JetPolynomial.Base))) (hTS : MapsTo e e.source S)
    (hST : baseEquiv '' closure (S : Set JetPolynomial.Base) ⊆ T)
    (K : Set JetPolynomial.Base) (hK : IsCompact K) (hKS : K ⊆ S)
    (hKt : K ⊆ e.target)
    (hKA : e.symm '' K ⊆ (A₀.chartWeightCompact i : Set JetPolynomial.Base))
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    (haoff : ∀ p ∉ K, a (baseEquiv p) = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0)

    (h : SmoothMetric M)
    (htarget : h.inner = g.inner + A₀.bundleRestore A₀.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)))
    {C : Set JetPolynomial.Base} (hC : IsCompact C)
    (hCS : C ⊆ (S : Set JetPolynomial.Base) ∩ e.target)
    (hCurveC : ∀ j x, x ∈ Curves j → baseEquiv.symm x ∈ C)
    (hactiveC : ∀ p ∈ C, A₀.chartWeight i (e.symm p) ≠ 0)
    (hEC : ∀ x ∈ E, baseEquiv.symm x ∈ C)
    (hold : ∀ j, ∀ x ∈ Curves j, a x = 0 →
      0 < ((SmallModes.coordDeriv SmallModes.dy (SmallModes.coordDeriv SmallModes.dx
        (A₀.phaseRealChartMap i e.symm F)) x ⬝ᵥ
        normalize (realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy x))*b j x +
        Real.sqrt (realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy x ⬝ᵥ
          realSecondForm (A₀.phaseRealChartMap i e.symm F) SmallModes.dy SmallModes.dy x)*c j x)^2 + (coordinateGauss (fun y => A₀.phaseMetricRead i e.symm h y 0)
        (fun y => A₀.phaseMetricRead i e.symm h y 1)
        (fun y => A₀.phaseMetricRead i e.symm h y 2) x)*(b j x)^2)
 :
    ∀ ε : ℝ, 0 < ε → ∀ ζ : ℝ, 0 < ζ → ∀ ηpos : ℝ, 0 < ηpos →
    ∃ z : ℝ, 0 < z ∧ z < ζ ∧ z ≤ 1 ∧ ∃ W : M → Space,
      IsSmoothIsometricEmbedding h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      (∀ p, dist (W p) (F p) < ηpos) ∧
      (∀ p ∈ C, AnalyticFirstProfileEstimate
        (A₀.phaseRealChartMap i e.symm F) (A₀.phaseRealChartMap i e.symm W)
        (baseEquiv p) ε) ∧
      (∀ p ∈ C, realBoundaryProfile (A₀.phaseRealChartMap i e.symm W) z (baseEquiv p) ∈
        regularBoundaryProfiles) ∧
      (∀ j x, x ∈ Curves j →
        RealModes.realSecondForm (A₀.phaseRealChartMap i e.symm W) (b j x,c j x) (b j x,c j x) x ≠ 0 ∧
        VelocityFrame.normalize (RealModes.realSecondForm (A₀.phaseRealChartMap i e.symm W)
          (b j x,c j x) (b j x,c j x) x) ≠
          -profilePreferred (realBoundaryProfile (A₀.phaseRealChartMap i e.symm W) z x)) ∧
      (∀ x ∈ E, ∀ r s : ℝ, |r| ≤ slopeBound → |s| ≤ slopeBound →
        let H := A₀.phaseRealChartMap i e.symm W
        let κ := RealModes.coordinateGaussianCurvature
          (RealModes.realMetric H SmallModes.dx SmallModes.dx)
          (RealModes.realMetric H SmallModes.dx SmallModes.dy)
          (RealModes.realMetric H SmallModes.dy SmallModes.dy) x
        0 < orderedCrossing H (1,r) (1,s) x κ ∧ 0 < orderedCrossing H (1,s) (1,r) x κ ∧
        ((0 < RealModes.realSecondForm H (1,r) (1,r) x ⬝ᵥ profilePreferred (realBoundaryProfile H z x) ∧
          0 < RealModes.realSecondForm H (1,s) (1,s) x ⬝ᵥ profilePreferred (realBoundaryProfile H z x)) ∨
         (0 < RealModes.realSecondForm H (1,r) (1,r) x ⬝ᵥ RealModes.realSecondForm H (1,s) (1,s) x ∧
          ∃ w : NormalFrame.Vec, profilePreferred (realBoundaryProfile H z x) ⬝ᵥ w = 0 ∧
            0 < RealModes.realSecondForm H (1,r) (1,r) x ⬝ᵥ w ∧
            0 < RealModes.realSecondForm H (1,s) (1,s) x ⬝ᵥ w))) ∧
      ∃ G : M → Space, ∃ _hG : ContMDiff planeModel spaceModel ∞ G,
        A₀.WeightedBound 1 3 ε (G-F) ∧
        ∃ V : M → Space, ContMDiff planeModel spaceModel ∞ V ∧
          A₀.WeightedBound 1 2 (z^8) (W-V) ∧
          (∀ p ∉ tsupport (A₀.weight i), V =ᶠ[𝓝 p] G) ∧
        ∀ p ∉ A₀.phaseSurfaceSupport i e K, V =ᶠ[𝓝 p] G := by

  classical
  have hKCS : K ∪ C ⊆ (S : Set JetPolynomial.Base) :=
    union_subset hKS (fun q hq => (hCS hq).1)
  have hKCt : K ∪ C ⊆ e.target := union_subset hKt (fun q hq => (hCS hq).2)
  have hKCA : e.symm '' (K ∪ C) ⊆ (A₀.chartWeightCompact i : Set JetPolynomial.Base) := by
    rintro _ ⟨q, hq, rfl⟩
    rcases hq with hqK | hqC
    · exact hKA ⟨q, hqK, rfl⟩
    · rw [← A₀.chartWeight_tsupport i]
      exact subset_tsupport _ (hactiveC q hqC)
  obtain ⟨Vprofile, hVprofile, hKCV, hCprofile, hCprofileS, _hVouter⟩ :=
    analytic_phase_profile_compact_neighborhood A₀ i e (hK.union hC) S.isOpen
      hKCS hKCt hKCA (houter i)
  have hKV : K ⊆ Vprofile := fun q hq => hKCV (Or.inl hq)
  have hCCprofile : C ⊆ closure Vprofile := fun q hq => subset_closure (hKCV (Or.inr hq))
  have hKU : baseEquiv '' K ⊆ U := by
    rintro _ ⟨q, hq, rfl⟩
    exact hTU (hST ⟨q, subset_closure (hKS hq), rfl⟩)
  obtain ⟨δ, ζembed, ηembed, hδ, hζembed, hηembed, htol⟩ :=
    analytic_primitive_embedding_tolerance A₀ houter hOld hFinj h i e hi hK hKt hKA hKU
      hI hHess hVprofile hKV
  intro ε hε ζ hζ ηpos hηpos
  let εstep := min ε δ
  have hεstep : 0 < εstep := lt_min hε hδ
  obtain ⟨z, hz, hzζ, hz1, W, hW, hgeometry, hposition, hprofiles, hregular,
      hcurves, hcrossing, G, hG, hslow, V, hV, hcorrection, hweightExterior, hexterior⟩ :=
    analytic_independent_preserving_circular_primitive_with_profiles data A₀ houter hF hmetric i e he hi
      hχ hχc hχs hcover ha hT hU hTU hn hI hN hHess haT hboundary
      hCurves hCurvesT hP hlocal hE hET haE slopeBound hSlope hb hc hbc
      S hSc hTS hST K hK hKS hKA hone haoff ℓ hℓx hℓy h htarget
      hC hCS hCurveC hactiveC hEC hCprofile hCprofileS hCCprofile hold
      εstep hεstep (min ζ ζembed) (lt_min hζ hζembed)
      (min ηpos ηembed) (lt_min hηpos hηembed)
  have hWlocal : IsSmoothIsometricMap h W := analytic_isometry_iff_local_spec.mp hW
  have hphaseδ : ∀ q ∈ closure Vprofile, AnalyticFirstProfileEstimate
      (A₀.phaseRealChartMap i e.symm F) (A₀.phaseRealChartMap i e.symm W)
      (baseEquiv q) δ := by
    intro q hq
    obtain ⟨w, hwU, hwV, herrorX, herrorY⟩ := hprofiles q hq
    exact ⟨w, hwU, hwV, herrorX.trans (min_le_right ε δ),
      herrorY.trans (min_le_right ε δ)⟩
  have hslowδ : A₀.WeightedBound 1 3 δ (G-F) :=
    fun j => (hslow j).mono_const (min_le_right ε δ)
  have hclosed : Topology.IsClosedEmbedding W := htol z hz
    (hzζ.trans_le (min_le_right ζ ζembed)) hz1 G V W hG hV hWlocal
    hphaseδ hslowδ hcorrection hexterior
    (fun q => (hposition q).trans_le (min_le_right ηpos ηembed))
  refine ⟨z, hz, hzζ.trans_le (min_le_left ζ ζembed), hz1, W,
    ⟨hWlocal, hclosed.injective⟩, hgeometry,
    (fun q => (hposition q).trans_le (min_le_left ηpos ηembed)), ?_, ?_, hcurves, hcrossing,
    G, hG, (fun j => (hslow j).mono_const (min_le_left ε δ)),
    V, hV, hcorrection, hweightExterior, hexterior⟩
  · intro q hq
    obtain ⟨w, hwU, hwV, herrorX, herrorY⟩ := hprofiles q (hCCprofile hq)
    exact ⟨w, hwU, hwV, herrorX.trans (min_le_left ε δ),
      herrorY.trans (min_le_left ε δ)⟩
  · intro q hq
    exact hregular q (hCCprofile hq)

end

end R4Embedding
