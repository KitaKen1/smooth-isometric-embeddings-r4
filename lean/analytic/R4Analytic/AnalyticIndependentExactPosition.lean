import R4Analytic.AnalyticIndependentFastFamily
import OAI.Geometry.SurfaceImmersion.Atlas.CrossAtlasExactGeometry
import R4Analytic.AnalyticAtlasC0Bounds
import OAI.Geometry.SurfaceImmersion.Geometry.ExactGeometricFastFamily

/-! Exact correction in data.A, estimates in the independent phase atlas
A0, and global C-zero closeness on the identical exact W.
Pending compilation and transitive axiom audit. -/

namespace R4Embedding

open OAI.ClosedSurfaceR4 OAI.ClosedSurfaceR4.FiniteOrderSmoothing

/-! Actual finite-accuracy primitive immersions with a Riemannian target,
uniform first-jet bounds, and a uniform nonzero second-form margin. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
open JetPolynomial JetPolynomial.Perturbation RealModes
local instance analyticRetainedIndependentExactFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance analyticRetainedIndependentExactFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance analyticRetainedIndependentExactDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance analyticRetainedIndependentExactDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance analyticRetainedIndependentExactSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance analyticRetainedIndependentExactSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
variable {g : SmoothMetric M} {F : M → OAI.ClosedSurfaceR4.Space}

theorem analytic_independent_exact_phase_metric_with_position [T2Space M] (data : MetricGoodPhaseData g F) (A₀ : SmoothingAtlas M)
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
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![a q^2,0,0]) y))) :
    ∀ ε : ℝ, 0 < ε → ∀ ζ : ℝ, 0 < ζ → ∀ η : ℝ, 0 < η →
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ε ∧
    ∃ z : ℝ, 0 < z ∧ z < ζ ∧ z ≤ 1 ∧ ∃ V G : M → OAI.ClosedSurfaceR4.Space,
      ContMDiff planeModel spaceModel ∞ V ∧
      AnalyticPhasePrimitiveProfileNearWithPosition A₀ F i e hi l S ℓ K ρ z V ∧
      IsSmoothIsometricImmersion M h G ∧ Nonempty (MetricGoodPhaseData h G) ∧
      A₀.WeightedBound 1 2 (z^8) (G-V) ∧
      (∀ p, dist (G p) (F p) < η) := by
  obtain ⟨V₀,R,c,b,hV₀,hR,hc,hb,hfamily⟩ := analytic_independent_profiled_fast_family_with_position data
    A₀ houter hF hmetric i e he hi hχ hχc hχs hcover l ha hamp S hSc hTS
    hQ hQO hFQ K hK hKS hKA hone hv ℓ hℓx hℓy h htarget
  intro ε hε ζ hζ η hη
  let n : ℝ := Fintype.card A₀.centers
  have hn : 0 ≤ n := Nat.cast_nonneg _
  let τ := η / (4 * (n + 1))
  have hden : 0 < 4 * (n + 1) := by positivity
  have hτ : 0 < τ := div_pos hη hden
  let ρ := min ε τ
  have hρ : 0 < ρ := lt_min hε hτ
  have hρε : ρ ≤ ε := min_le_left _ _
  have hρτ : ρ ≤ τ := min_le_right _ _
  obtain ⟨δ,hδ,_,hsmall⟩ := ExactCorrection.positive_power_threshold 1 8 τ (by norm_num) hτ
  obtain ⟨z,hz,hzcap,hz1,V,W,hV,hnear,hW,hgood,hcorrection⟩ :=
    data.A.exact_geometric_metric_with_property_in_atlas A₀ h data.outer_locally_one R c b V₀ hc hb hV₀
      (AnalyticPhasePrimitiveProfileNearWithPosition A₀ F i e hi l S ℓ K ρ)
      (hfamily ρ hρ) (min δ ζ) (lt_min hδ hζ)
  have hzδ := hzcap.trans_le (min_le_left _ _)
  have hzζ := hzcap.trans_le (min_le_right _ _)
  have hpower : z^8 < τ := by
    simpa only [Real.rpow_ofNat, one_mul] using hsmall z hz hzδ
  refine ⟨ρ,hρ,hρε,z,hz,hzζ,hz1,V,W,hV,hnear,hW,hgood,hcorrection,?_⟩
  obtain ⟨G,hG,hGO,hslow,hfast,hprofile,hext,hextK⟩ := hnear
  have hslowτ : A₀.WeightedBound 1 3 τ (G-F) := fun j => (hslow j).mono_const hρτ
  have hfastτ : A₀.WeightedBound 1 0 τ (V-G) := fun j => (hfast j).mono_const hρτ
  have hbudget : 3 * n * τ < η := by
    have hηeq : (4 * (n + 1)) * τ = η := by
      dsimp only [τ]
      exact mul_div_cancel₀ η hden.ne'
    nlinarith [mul_nonneg hn hτ.le]
  intro p
  have hbound := analytic_same_output_dist_le A₀ hτ.le hτ.le
    (pow_nonneg hz.le 8) hslowτ hfastτ hcorrection p
  apply lt_of_le_of_lt hbound
  change n * (τ + τ + z^8) < η
  have hle : n * (τ + τ + z^8) ≤ 3 * n * τ := by
    nlinarith [mul_le_mul_of_nonneg_left hpower.le hn]
  exact hle.trans_lt hbudget

end

end R4Embedding
