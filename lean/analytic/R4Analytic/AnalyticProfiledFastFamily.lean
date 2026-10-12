import R4Analytic.AnalyticProfiledRealization
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasMetricJetMargins
import OAI.Geometry.SurfaceImmersion.Geometry.ExactFastFamily

namespace R4Embedding

open OAI.ClosedSurfaceR4 OAI.ClosedSurfaceR4.FiniteOrderSmoothing

/-! Actual fast approximants with prescribed accuracy in the leading five
primitive derivatives and the slow baseline, retained for the exact step. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
open JetPolynomial JetPolynomial.Perturbation RealModes PrimitiveRealization CovarianceCorrector
local instance profiledPhasePrimitiveFamilyFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance profiledPhasePrimitiveFamilyFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance profiledPhasePrimitiveFamilyDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance profiledPhasePrimitiveFamilyDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance profiledPhasePrimitiveFamilySectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance profiledPhasePrimitiveFamilySectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)


def AnalyticPhasePrimitiveProfileNearWithPosition (A : SmoothingAtlas M) (F : M → OAI.ClosedSurfaceR4.Space) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm)
    {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)
    (S : TopologicalSpace.Opens JetPolynomial.Base) (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (K : Set JetPolynomial.Base) (ε z : ℝ) (V : M → OAI.ClosedSurfaceR4.Space) : Prop :=
  ∃ G : M → OAI.ClosedSurfaceR4.Space, ∃ hG : ContMDiff planeModel spaceModel ∞ G,
    ∃ hGO : MapsTo (lowJet (A.jetChartMap i G ∘ e.symm)) S O,
    A.WeightedBound 1 3 ε (G-F) ∧
    A.WeightedBound 1 0 ε (V-G) ∧
    (∀ p ∈ (S : Set JetPolynomial.Base) ∩ e.target,
      let geom := l.geometry (A.jetChartMap i G ∘ e.symm) ((A.jetChartMap_smooth i hG).comp hi) hGO
      let t : Period := ((ℓ p/z : ℝ) : Period)
      ‖SurfaceVelocityFamily.Loop.primitiveJetProfile (A.vectorChartRead i V ∘ e.symm) z p-
        ![geom.longitudinal.val p t,geom.Y p,geom.C p,
          (geom.longitudinal.slow (coordinateVector 1)).val p t,geom.V.angle.val p t]‖ ≤ ε) ∧
    (∀ p ∉ tsupport (A.weight i), V =ᶠ[𝓝 p] G) ∧
    ∀ p ∉ A.phaseSurfaceSupport i e K, V =ᶠ[𝓝 p] G

variable {g : SmoothMetric M} {F : M → OAI.ClosedSurfaceR4.Space}

theorem analytic_profiled_fast_family_with_position (data : MetricGoodPhaseData g F)
    (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
    (i : data.A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
    (hcover : (data.A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source)
    {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)
    {a : JetPolynomial.Base → ℝ} (ha : ContDiff ℝ ∞ a) (hamp : l.HasSpatialAmplitude a)
    (S : TopologicalSpace.Opens JetPolynomial.Base)
    (hSc : IsCompact (closure (S : Set JetPolynomial.Base))) (hTS : MapsTo e e.source S)
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (hFQ : MapsTo (lowJet (data.A.jetChartMap i F ∘ e.symm)) S Q)
    (K : Set JetPolynomial.Base) (hK : IsCompact K) (hKS : K ⊆ S)
    (hKA : e.symm '' K ⊆ (data.A.chartWeightCompact i : Set JetPolynomial.Base))
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    (hv : ∀ J ∈ O, lowJetPosition J ∉ K → ∀ t, l.velocity (J,t) = SurfaceVelocityFamily.normal J)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0)

    (h : SmoothMetric M)
    (htarget : h.inner = g.inner + data.A.bundleRestore data.A.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![a q^2,0,0]) y))) :
    ∃ V₀ R₁ c₁ c₂ : ℝ, 0 ≤ V₀ ∧ 0 < R₁ ∧ 0 < c₁ ∧ 0 < c₂ ∧ ∀ ε : ℝ, 0 < ε →
      data.A.GeometricFastFamilyWithProperty h R₁ c₁ c₂ V₀
        (AnalyticPhasePrimitiveProfileNearWithPosition data.A F i e hi l S ℓ K ε) := by
  obtain ⟨ρ,R₁,c₁,hρ,hR₁,hc₁,hjet⟩ := data.A.metric_firstJet_margin h
  obtain ⟨c,c₂,V₀,hc,hc₂,hV₀,hfamilies⟩ := analytic_profiled_realization_with_position data
    hF hmetric i e he hi hχ hχc hχs hcover l ha hamp S hSc hTS
    hQ hQO hFQ K hK hKS hKA hone hv ℓ hℓx hℓy
  refine ⟨V₀,R₁,c₁,c₂,hV₀,hR₁,hc₁,hc₂,?_⟩
  intro ε hε N
  obtain ⟨lp,lm,b,u,η,L,C,Cv,Dp,D₀,P,hb,_,hu,hη,hη1,hL,hC,hCv,_,_,hblp,hblm,hP,hfamily⟩ :=
    hfamilies 442 (N+1)
  obtain ⟨η₀,hη₀,_,hsmall⟩ := ExactCorrection.positive_power_threshold C (N+1) ρ
    (by positivity) hρ
  obtain ⟨ηs,hηs,_,hslow⟩ := ExactCorrection.positive_power_threshold L u ε hu hε
  obtain ⟨ηp,hηp,_,hprofile⟩ := primitive_normal_threshold hb hblp hε Dp
  obtain ⟨ηv,hηv,_,hposition⟩ := primitive_normal_threshold hb hblm hε D₀
  refine ⟨min η (min η₀ (min ηs (min ηp ηv))),C,Cv,
    lt_min hη (lt_min hη₀ (lt_min hηs (lt_min hηp hηv))),hC,hCv,?_⟩
  intro z hz hzη
  have hzbase := hzη.trans_le (min_le_left _ _)
  have hzother := hzη.trans_le (min_le_right _ _)
  have hzmetric := hzother.trans_le (min_le_left _ _)
  have hzprofiles := hzother.trans_le (min_le_right _ _)
  have hzslow := hzprofiles.trans_le (min_le_left _ _)
  have hzboth := hzprofiles.trans_le (min_le_right _ _)
  have hzprofile := hzboth.trans_le (min_le_left _ _)
  have hzposition := hzboth.trans_le (min_le_right _ _)
  obtain ⟨G,V,hG,hV,hclose,hfast,hmap,hweighted,hzeroV,hshift,herror,hI,hB,hBmargin,hN,hext,hextK,hGs,hGO,hprof⟩ :=
    hfamily z hz hzbase
  have herr : data.A.TensorWeightedBound 1 440 (C*z^(N+1)) (inducedTensor V-h.inner) := by
    rw [htarget]
    exact fun j => (herror j).mono_order (by omega)
  have hexp : (N : ℝ)+1 = ((N+1 : ℕ) : ℝ) := by norm_num
  have hjet' := hjet V hV (C*z^(N+1)) (by positivity)
    (by simpa only [hexp,Real.rpow_natCast] using hsmall z hz hzmetric)
    (fun j => (herr j).mono_order (by omega))
  refine ⟨V,hV,?_,hzeroV,hweighted,(fun j k hk x => hshift j k (by omega) x),herr,?_⟩
  · refine ⟨G,hGs,hGO,?_,?_,?_,hext,hextK⟩
    · exact fun j => (hclose j).mono_const (hslow z hz hzslow).le
    · exact fun j => (hfast j).mono_const (hposition z hz hzposition).le
    · intro p hp
      exact (hprof p hp).trans (hprofile z hz hzprofile).le
  · intro j x hx
    exact ⟨(hjet' j x hx).1,(hjet' j x hx).2,(hBmargin j x hx).le⟩


end

end R4Embedding
