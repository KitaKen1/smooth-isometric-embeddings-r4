import R4Analytic.AnalyticIndependentOriginalProfiles
import OAI.Geometry.SurfaceImmersion.Primitive.PhaseBoundaryProfile
import OAI.Geometry.SurfaceImmersion.Primitive.ExactPhaseOriginalProfiles
import OAI.Geometry.SurfaceImmersion.Primitive.PhaseLeadingProfileStability
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveProfileStability
import OAI.Geometry.SurfaceImmersion.Geometry.ExactGeometricFastFamily
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveMetric
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasMetricJetMargins

/-! Retain the same exact W and its global position estimate through
the independent phase-atlas profile conversion.
Pending compilation and transitive axiom audit. -/

namespace R4Embedding

open OAI.ClosedSurfaceR4 OAI.ClosedSurfaceR4.FiniteOrderSmoothing

/-! Actual finite-accuracy primitive immersions with a Riemannian target,
uniform first-jet bounds, and a uniform nonzero second-form margin. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector GeometryPreservation
local instance analyticIndependentExactPhaseBoundaryProfilesFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance analyticIndependentExactPhaseBoundaryProfilesFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance analyticIndependentExactPhaseBoundaryProfilesDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance analyticIndependentExactPhaseBoundaryProfilesDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance analyticIndependentExactPhaseBoundaryProfilesSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance analyticIndependentExactPhaseBoundaryProfilesSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
variable {g : SmoothMetric M} {F : M → OAI.ClosedSurfaceR4.Space}

theorem analytic_independent_exact_phase_boundary_profiles_with_position [T2Space M] (data : MetricGoodPhaseData g F) (A₀ : SmoothingAtlas M)
    (houter : ∀ i x, x ∈ tsupport (A₀.weight i) → A₀.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
    (i : A₀.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
    (hcover : (A₀.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source)
    {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)
    {a : JetPolynomial.Base → ℝ} (ha : ContDiff ℝ ∞ a) (hamp : l.HasSpatialAmplitude a)
    (S : TopologicalSpace.Opens JetPolynomial.Base)
    (hSc : IsCompact (closure (S : Set JetPolynomial.Base))) (hTS : MapsTo e e.source S)
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (hFQ : MapsTo (lowJet (A₀.jetChartMap i F ∘ e.symm)) S Q)
    (K : Set JetPolynomial.Base) (hK : IsCompact K) (hKS : K ⊆ S)
    (hKA : e.symm '' K ⊆ (A₀.chartWeightCompact i : Set JetPolynomial.Base))
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    (hv : ∀ J ∈ O, lowJetPosition J ∉ K → ∀ t, l.velocity (J,t) = SurfaceVelocityFamily.normal J)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0)

    (h : SmoothMetric M)
    (htarget : h.inner = g.inner + A₀.bundleRestore A₀.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![a q^2,0,0]) y)))
    {C : Set JetPolynomial.Base} (hC : IsCompact C)
    (hCS : C ⊆ (S : Set JetPolynomial.Base) ∩ e.target) :
    ∀ ε : ℝ, 0 < ε → ∀ ζ : ℝ, 0 < ζ → ∀ ηpos : ℝ, 0 < ηpos →
    ∃ z : ℝ, 0 < z ∧ z < ζ ∧ z ≤ 1 ∧ ∃ W : M → OAI.ClosedSurfaceR4.Space,
      IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      (∀ p, dist (W p) (F p) < ηpos) ∧
      (∀ p ∈ C,
        ‖realBoundaryProfile (A₀.phaseRealChartMap i e.symm W) z (SurfaceJetCoordinates.baseEquiv p)-
          boundaryProfileMap (l.geometricLeadingProfile (A₀.jetChartMap i F ∘ e.symm)
            ((A₀.jetChartMap_smooth i hF).comp hi)
            (fun _ hp => hQO (hFQ hp)) p ((ℓ p/z : ℝ) : Period))‖ < ε) ∧
      ∃ G : M → OAI.ClosedSurfaceR4.Space, ∃ _hG : ContMDiff planeModel spaceModel ∞ G,
        A₀.WeightedBound 1 3 ε (G-F) ∧
        ∃ V : M → OAI.ClosedSurfaceR4.Space, ContMDiff planeModel spaceModel ∞ V ∧
          A₀.WeightedBound 1 2 (z^8) (W-V) ∧
          (∀ p ∉ tsupport (A₀.weight i), V =ᶠ[𝓝 p] G) ∧
        ∀ p ∉ A₀.phaseSurfaceSupport i e K, V =ᶠ[𝓝 p] G := by
  have hall := analytic_independent_exact_phase_original_profiles_with_position data A₀ houter hF hmetric i e he hi hχ hχc hχs hcover
    l ha hamp S hSc hTS hQ hQO hFQ K hK hKS hKA hone hv ℓ hℓx hℓy h htarget hC hCS
  intro ε hε ζ hζ ηpos hηpos
  let δ := ε/(‖boundaryProfileMap‖+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨z,hz,hzζ,hz1,W,hW,hgeometry,hposition,hprofiles,G,hG,hslow,V,hV,hcorrection,hext⟩ :=
    hall δ hδ ζ hζ ηpos hηpos
  refine ⟨z,hz,hzζ,hz1,W,hW,hgeometry,hposition,?_,G,hG,?_,V,hV,hcorrection,hext⟩
  · intro p hp
    exact A₀.phaseRealChartMap_profile_error i hi hW.1 z p _ hε (hprofiles p hp)
  · exact fun j => (hslow j).mono_const (div_le_self hε.le (by linarith [norm_nonneg boundaryProfileMap]))


end

end R4Embedding
