import R4Analytic.AnalyticIndependentRealizationEmbedding
import R4Analytic.AnalyticPreparedStartingEmbedding
import OAI.Geometry.SurfaceImmersion.Geometry.UniformCorrectedTermC1
import OAI.Geometry.SurfaceImmersion.Geometry.ReferenceBoundaryStartingFamily
import OAI.Geometry.SurfaceImmersion.Geometry.UniformScaledPathBounds
import OAI.Geometry.SurfaceImmersion.Geometry.CycleCorrectedGeometry
import OAI.Geometry.SurfaceImmersion.Primitive.IndependentCircularRealization

/-! Join the actual prepared starting embedding, corrected cycles, prefix
bounds and embedding-preserving independent realization on identical maps.
This is a conditional input theorem. Existence of its spherical embedding
input for every orientable smooth surface remains a separate obligation.
Pending compilation and transitive axiom audit. -/

namespace R4Embedding

open OAI.ClosedSurfaceR4 OAI.ClosedSurfaceR4.FiniteOrderSmoothing

/-! Smooth isometric embeddings constructed from an actual smooth spherical
embedding. Initial spherical embedding existence is not asserted here. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
local instance retainedSphericalEmbedding_mainFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance retainedSphericalEmbedding_mainFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance retainedSphericalEmbedding_mainDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance retainedSphericalEmbedding_mainDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance retainedSphericalEmbedding_mainSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance retainedSphericalEmbedding_mainSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

/-- The actual global construction starting from a smooth unit spherical embedding. All
primitive amplitudes and the starting scale are chosen uniformly before
selecting the finite crossings. -/
theorem analytic_isometric_embedding_of_spherical_embedding (g : SmoothMetric M)
    {I : M → Space} (hI : ContMDiff planeModel spaceModel ∞ I)
    (hunit : ∀ p, ‖I p‖ = 1)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel I p))
    (hIinj : Function.Injective I) :
    ∃ W : M → Space, IsSmoothIsometricEmbedding g W := by
  classical
  obtain ⟨A⟩ := exists_smoothingAtlas (M := M)
  obtain ⟨r,D,c,hr,hr1,hD,hc,_hIb,_hIm,hIs,hstart⟩ :=
    analytic_reference_circular_starting_embeddings A g hI hunit hImm hIinj zero_lt_one
  let gref := A.shortRemainderMetric g (space_smul_contMDiff hI r) hIs
  have href : gref.inner = g.inner-inducedTensor (r • I) := rfl
  obtain ⟨C,hC,hpath⟩ := A.uniform_scaled_path_bound g r hD
  obtain ⟨d⟩ := A.exists_reference_circular_atlas gref g hc (show 0 ≤ C+1 by linarith)
  obtain ⟨pt,wt,mt,hpt,hwt,hmt,hterm⟩ := d.uniform_corrected_term_C1 hI r href hD
  let m := Fintype.card (d.B.centers × Fin 3)
  let e : Fin m ≃ (d.B.centers × Fin 3) := (Fintype.equivFin _).symm
  obtain ⟨mapTol,delta,W,hmapTol,hmapLe,_hdelta,_hdeltaR,hW,hcycles⟩ :=
    d.corrected_cycles hI r href hpt hwt hmt e
  obtain ⟨E,hE,hterms⟩ := hterm (W 1) (hW 1)
  obtain ⟨N,hN,hrealize⟩ := analytic_independent_circular_embedding_realization A g c C d.B
    d.radius d.L (fun i => ‖(d.P i).ξ‖+1) d.L_pos d.region
    d.weight_nonneg d.weight_positive d.convex m E hE
  obtain ⟨q,hindex,houter,_hchart,hpart,hell,hphase,hweights,hweightClose,hcorrect⟩ :=
    hcycles N hN
  obtain ⟨G,g₀,normal,hG,_hu,hG₀,hGclosed,hg₀,⟨good⟩,_hn,hnear,hGb,hlower,_hgm,hshort,hgeom⟩ :=
    hstart (N*m) d.B q mapTol hmapTol
  obtain ⟨f,dCirc,hamp,hphi,hcurves,_hrad,_houter',_hchart',hlinear,hconvex,hcycle,hcyclePhase,_htotal⟩ :=
    hcorrect G hG hnear
  have hnear' : A.WeightedBound 1 1 mt (G-I) :=
    fun i => (hnear i).mono_const hmapLe
  have hcopy (k : Fin N) (b : d.B.centers × Fin 3) :
      (finProdFinEquiv (k,e.symm b)).divNat = k ∧
        e (finProdFinEquiv (k,e.symm b)).modNat = b := by
    have hh := Prod.mk.inj (finProdFinEquiv.symm_apply_apply (k,e.symm b))
    exact ⟨hh.1,by rw [hh.2,e.apply_symm_apply]⟩
  have hell' (k : Fin N) (i : d.B.centers) (j : Fin 3) :
      ‖d.cycleLinearParts e q k i j-(d.P i).ξ j‖ < pt := by
    have h := hphase (finProdFinEquiv (k,e.symm (i,j)))
    simpa only [ReferenceCircularAtlas.cycleLinearParts,
      (hcopy k (i,j)).2] using h
  have htermBound (k : Fin N) (a : Fin m) :
      A.TensorWeightedBound 1 1 E ((f k).term a) := by
    let f' := (f k).reindex e.symm
    have hp' : f'.phase = d.perturbedPhases (d.cycleLinearParts e q k) := by
      funext b
      exact (hphi k (e.symm b)).trans (congrArg _ (e.apply_symm_apply b))
    have ha' : f'.amplitude = d.B.correctedPrimitiveAmplitude d.basis
        (d.cycleWeights e q k) (d.perturbedPhases (d.cycleLinearParts e q k))
        (g.inner-inducedTensor (r • G)) := by
      funext b
      exact (hamp k (e.symm b)).trans (congrArg _ (e.apply_symm_apply b))
    have hnon (b : d.B.centers × Fin 3) :
        ContMDiff planeModel 𝓘(ℝ) ∞ (d.cycleWeights e q k b) := by
      let a : Fin (N*m) := finProdFinEquiv (k,e.symm b)
      have hh : e a.modNat = b := (hcopy k b).2
      have hrsmall : (q.radius a)^2 < (d.radius b.1)^2 := by
        have hrpos := q.radius_pos a
        have hro := q.radius_outer a
        rw [houter a,hh] at hro
        nlinarith [d.radius_pos b.1]
      exact (shrinkingCircularWeight_smooth (b.1 : M) (d.B.weight b.1)
        (d.B.weight_smooth b.1) (d.region b.1) hrsmall).1
    have hsupp (b : d.B.centers × Fin 3) :
        tsupport (d.cycleWeights e q k b) ⊆ tsupport (d.B.weight b.1) := by
      apply closure_mono
      intro p hp
      change d.cycleWeights e q k b p ≠ 0 at hp
      change d.B.weight b.1 p ≠ 0
      intro hz
      exact hp (by simp only [ReferenceCircularAtlas.cycleWeights,shrinkingCircularWeight,hz,zero_mul])
    have hb := hterms (d.cycleLinearParts e q k) (d.cycleWeights e q k) (hell' k)
      hnon hsupp (hweightClose k) (fun b => hweights k b 1) G hG hnear' hGb f' hp' ha' (e a)
    change A.TensorWeightedBound 1 1 E ((f k).term (e.symm (e a))) at hb
    simpa only [e.symm_apply_apply] using hb
  have hshort' : ∀ p v, inducedForm (r • G) p v v ≤ (1/2 : ℝ)*g.inner p v v := by
    intro p v
    change inducedTensor (r • G) p v v ≤ _
    rw [← hg₀]
    exact hshort p v
  have hpBound (k : Fin N) : A.TensorWeightedBound 1 1 C
      (g₀.inner+((k.val : ℝ)/(N : ℝ)) • (g.inner-inducedTensor (r • G))) := by
    rw [hg₀]
    exact hpath G hG hGb (hG₀.mfderiv_injective) hshort' _
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      ((div_le_one (by exact_mod_cast hN)).mpr (by exact_mod_cast k.isLt.le))
  have hcv (a : Fin (N*m)) : dCirc.convexPart a = d.L (dCirc.curves a).index := by
    rw [hconvex,hpart,hcurves,hindex]
  have hlin (a : Fin (N*m)) : ‖dCirc.linearPart a‖ ≤ ‖(d.P (dCirc.curves a).index).ξ‖+1 := by
    rw [hlinear,hcurves,hindex]
    exact hell a
  have htarget : g.inner = g₀.inner+(g.inner-inducedTensor (r • G)) := by
    rw [hg₀]
    abel
  have hgeom' : FiniteBoundaryGeometry dCirc.curves
      (boundaryCrossingSet dCirc.curves univ) (r • G) normal := by
    rw [hcurves]
    exact hgeom
  obtain ⟨F,hF,_hgood⟩ := hrealize g₀ hlower _ f htermBound hpBound dCirc
    hcycle hcyclePhase hcv hlin g htarget (r • G) normal
      ⟨analytic_isometry_iff_local_spec.mp hG₀,hGclosed.injective⟩ good hgeom'
  exact ⟨F,hF⟩


end

end R4Embedding
