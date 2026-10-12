import R4Embedding.SphericalTransfer
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Data.Fintype.EquivFin

/-! Assemble embeddings on the finitely many clopen components of a compact
surface. Componentwise existence remains an explicit input. -/

noncomputable section
namespace R4Embedding

open Manifold Set TopologicalSpace
open scoped ContDiff

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

local instance surfaceLocallyConnected : LocallyConnectedSpace M :=
  ChartedSpace.locallyConnectedSpace Plane M

def componentOpen (c : ConnectedComponents M) : Opens M :=
  ⟨ConnectedComponents.mk ⁻¹' {c},
    (isOpen_discrete {c}).preimage ConnectedComponents.continuous_coe⟩

theorem componentOpen_closed (c : ConnectedComponents M) :
    IsClosed (componentOpen c : Set M) :=
  isClosed_singleton.preimage ConnectedComponents.continuous_coe

instance componentOpenCompact [CompactSpace M] (c : ConnectedComponents M) :
    CompactSpace (componentOpen c) :=
  isCompact_iff_compactSpace.mp (componentOpen_closed c).isCompact

theorem componentOpen_connected (c : ConnectedComponents M) :
    ConnectedSpace (componentOpen c) := by
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
  apply isConnected_iff_connectedSpace.mp
  change IsConnected (ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk p})
  rw [connectedComponents_preimage_singleton]
  exact isConnected_connectedComponent

instance componentOpenConnected (c : ConnectedComponents M) : ConnectedSpace (componentOpen c) :=
  componentOpen_connected c

theorem surface_components_finite [CompactSpace M] : Finite (ConnectedComponents M) :=
  inferInstance

def componentAssembly {E : Type*} (f : (c : ConnectedComponents M) → componentOpen c → E)
    (p : M) : E :=
  f (ConnectedComponents.mk p) ⟨p, rfl⟩

theorem componentAssembly_restrict {E : Type*}
    (f : (c : ConnectedComponents M) → componentOpen c → E)
    (c : ConnectedComponents M) (p : componentOpen c) :
    componentAssembly f p.val = f c p := by
  rcases p with ⟨p, hp⟩
  change ConnectedComponents.mk p = c at hp
  subst c
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem componentAssembly_contMDiff
    {f : (c : ConnectedComponents M) → componentOpen c → E}
    (hf : ∀ c, ContMDiff planeModel 𝓘(ℝ, E) ∞ (f c)) :
    ContMDiff planeModel 𝓘(ℝ, E) ∞ (componentAssembly f) := by
  intro p
  let c := ConnectedComponents.mk p
  let q : componentOpen c := ⟨p, rfl⟩
  have hsub : ContMDiff planeModel 𝓘(ℝ, E) ∞
      (fun q : componentOpen c => componentAssembly f q.val) := by
    simpa only [componentAssembly_restrict] using hf c
  exact contMDiffAt_subtype_iff.mp (hsub q)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem componentAssembly_injective
    {f : (c : ConnectedComponents M) → componentOpen c → E}
    (hf : ∀ c, Function.Injective (f c))
    (hsep : ∀ c d, c ≠ d → ∀ p q, f c p ≠ f d q) :
    Function.Injective (componentAssembly f) := by
  intro p q hpq
  have hc : ConnectedComponents.mk p = ConnectedComponents.mk q := by
    by_contra hne
    exact hsep _ _ hne ⟨p, rfl⟩ ⟨q, rfl⟩ hpq
  let c := ConnectedComponents.mk p
  let p' : componentOpen c := ⟨p, rfl⟩
  let q' : componentOpen c := ⟨q, hc.symm⟩
  have heq : f c p' = f c q' := by
    calc
      f c p' = componentAssembly f p := (componentAssembly_restrict f c p').symm
      _ = componentAssembly f q := hpq
      _ = f c q' := componentAssembly_restrict f c q'
  exact congrArg Subtype.val (hf c heq)

variable [IsManifold planeModel ∞ M]

open IsManifold

theorem openSubtype_mfderiv_surjective (U : Opens M) (p : U) :
    Function.Surjective (mfderiv planeModel planeModel (Subtype.val : U → M) p) := by
  let : FiniteDimensional ℝ (TangentSpace planeModel p) :=
    inferInstanceAs (FiniteDimensional ℝ Plane)
  let : FiniteDimensional ℝ (TangentSpace planeModel (p.val : M)) :=
    inferInstanceAs (FiniteDimensional ℝ Plane)
  let A := mfderiv planeModel planeModel (Subtype.val : U → M) p
  have hinj : Function.Injective A :=
    (IsImmersion.of_opens (I := planeModel) (n := ∞) U).injective_mfderiv (by simp) p
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := A.toLinearMap) (by rfl)).mp hinj

theorem componentAssembly_mfderiv_injective
    {f : (c : ConnectedComponents M) → componentOpen c → E}
    (hf : ∀ c, ContMDiff planeModel 𝓘(ℝ, E) ∞ (f c))
    (himm : ∀ c p, Function.Injective (mfderiv planeModel 𝓘(ℝ, E) (f c) p))
    (p : M) : Function.Injective (mfderiv planeModel 𝓘(ℝ, E) (componentAssembly f) p) := by
  let c := ConnectedComponents.mk p
  let q : componentOpen c := ⟨p, rfl⟩
  have heq : (componentAssembly f) ∘ (Subtype.val : componentOpen c → M) = f c := by
    funext q
    exact componentAssembly_restrict f c q
  have hchain := mfderiv_comp q
    ((componentAssembly_contMDiff hf p).mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (I := planeModel) (n := ∞) q).mdifferentiableAt (by simp))
  rw [heq] at hchain
  intro v w hvw
  obtain ⟨v', hv'⟩ := openSubtype_mfderiv_surjective (componentOpen c) q v
  obtain ⟨w', hw'⟩ := openSubtype_mfderiv_surjective (componentOpen c) q w
  have hpre : v' = w' := by
    apply himm c q
    have hv'' := congrArg (mfderiv planeModel 𝓘(ℝ, E) (componentAssembly f) p) hv'
    have hw'' := congrArg (mfderiv planeModel 𝓘(ℝ, E) (componentAssembly f) p) hw'
    exact (congrArg (fun A => A v') hchain).trans
      (hv''.trans (hvw.trans (hw''.symm.trans (congrArg (fun A => A w') hchain.symm))))
  exact hv'.symm.trans ((congrArg _ hpre).trans hw')

theorem translation_mvfderiv {N : Type*} [TopologicalSpace N] [ChartedSpace Plane N]
    {f : N → E} (hf : ContMDiff planeModel 𝓘(ℝ, E) ∞ f) (b : E) (p : N) :
    mvfderiv planeModel (fun q => f q + b) p = mvfderiv planeModel f p := by
  rw [mvfderiv_fun_add ((hf p).mdifferentiableAt (by simp)) mdifferentiableAt_const,
    mvfderiv_const, add_zero]

theorem translation_mfderiv_injective {N : Type*} [TopologicalSpace N]
    [ChartedSpace Plane N] {f : N → E}
    (hf : ContMDiff planeModel 𝓘(ℝ, E) ∞ f) (b : E)
    (himm : ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ, E) f p)) (p : N) :
    Function.Injective (mfderiv planeModel 𝓘(ℝ, E) (fun q => f q + b) p) := by
  intro v w hvw
  apply himm p
  apply (NormedSpace.fromTangentSpace (f p)).injective
  have h : mvfderiv planeModel (fun q => f q + b) p v =
      mvfderiv planeModel (fun q => f q + b) p w :=
    congrArg (NormedSpace.fromTangentSpace (f p + b)) hvw
  rw [translation_mvfderiv hf b p] at h
  exact h

omit [IsManifold planeModel ∞ M] in
theorem exists_component_translations [CompactSpace M]
    {f : (c : ConnectedComponents M) → componentOpen c → E}
    (hf : ∀ c, Continuous (f c)) (v : E) (hv : ‖v‖ = 1) :
    ∃ b : ConnectedComponents M → E,
      ∀ c d, c ≠ d → ∀ p q, f c p + b c ≠ f d q + b d := by
  classical
  let : Fintype (ConnectedComponents M) := Fintype.ofFinite _
  have hcompact : IsCompact (⋃ c, Set.range (f c)) :=
    isCompact_iUnion (fun c => isCompact_range (hf c))
  obtain ⟨B, hB, hbound⟩ := hcompact.isBounded.exists_pos_norm_le
  let e := Fintype.equivFin (ConnectedComponents M)
  let rank : ConnectedComponents M → ℝ := fun c => (e c).val
  let L := 2 * B + 1
  have hL : 0 < L := by dsimp [L]; linarith
  refine ⟨fun c => (L * rank c) • v, ?_⟩
  intro c d hne p q heq
  have hneRank : (e c).val ≠ (e d).val := by
    intro h
    exact hne (e.injective (Fin.ext h))
  have hrank : 1 ≤ |rank c - rank d| := by
    rcases lt_or_gt_of_ne hneRank with hlt | hgt
    · have hn : (e c).val + 1 ≤ (e d).val := by omega
      have hr : rank c + 1 ≤ rank d := by
        dsimp [rank]
        exact_mod_cast hn
      rw [abs_of_nonpos (by linarith : rank c - rank d ≤ 0)]
      linarith
    · have hn : (e d).val + 1 ≤ (e c).val := by omega
      have hr : rank d + 1 ≤ rank c := by
        dsimp [rank]
        exact_mod_cast hn
      rw [abs_of_nonneg (by linarith : 0 ≤ rank c - rank d)]
      linarith
  have hc : ‖f c p‖ ≤ B := hbound _ (mem_iUnion.mpr ⟨c, mem_range_self p⟩)
  have hd : ‖f d q‖ ≤ B := hbound _ (mem_iUnion.mpr ⟨d, mem_range_self q⟩)
  have hdiff : (L * rank c) • v - (L * rank d) • v = f d q - f c p := by
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using heq
  have hsmall : ‖(L * rank c) • v - (L * rank d) • v‖ ≤ 2 * B := by
    rw [hdiff]
    exact (norm_sub_le _ _).trans (by linarith)
  have hnorm : ‖(L * rank c) • v - (L * rank d) • v‖ = L * |rank c - rank d| := by
    rw [← sub_smul, norm_smul, hv, mul_one, ← mul_sub, Real.norm_eq_abs,
      abs_mul, abs_of_pos hL]
  rw [hnorm] at hsmall
  have hlarge := mul_le_mul_of_nonneg_left hrank hL.le
  dsimp [L] at hsmall hlarge
  linarith

theorem exists_embedding_of_component_embeddings [CompactSpace M]
    (v : E) (hv : ‖v‖ = 1)
    (hcomponent : ∀ c : ConnectedComponents M, ∃ f : componentOpen c → E,
      ContMDiff planeModel 𝓘(ℝ, E) ∞ f ∧ Function.Injective f ∧
      ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ, E) f p)) :
    ∃ F : M → E, ContMDiff planeModel 𝓘(ℝ, E) ∞ F ∧ Function.Injective F ∧
      ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ, E) F p) := by
  classical
  choose f hs hi hm using hcomponent
  obtain ⟨b, hb⟩ := exists_component_translations (fun c => (hs c).continuous) v hv
  let translated : (c : ConnectedComponents M) → componentOpen c → E :=
    fun c p => f c p + b c
  have ht : ∀ c, ContMDiff planeModel 𝓘(ℝ, E) ∞ (translated c) :=
    fun c => ((contDiff_id.add contDiff_const :
      ContDiff ℝ ∞ (fun x : E => x + b c)).contMDiff).comp (hs c)
  refine ⟨componentAssembly translated, componentAssembly_contMDiff ht, ?_, ?_⟩
  · apply componentAssembly_injective
    · intro c p q heq
      exact hi c (add_right_cancel heq)
    · exact hb
  · exact componentAssembly_mfderiv_injective ht
      (fun c => translation_mfderiv_injective (hs c) (b c) (hm c))

theorem exists_three_embedding_of_component_embeddings [CompactSpace M]
    (hcomponent : ∀ c : ConnectedComponents M, ∃ f : componentOpen c → ThreeSpace,
      ContMDiff planeModel threeModel ∞ f ∧ Function.Injective f ∧
      ∀ p, Function.Injective (mfderiv planeModel threeModel f p)) :
    ∃ F : M → ThreeSpace, ContMDiff planeModel threeModel ∞ F ∧ Function.Injective F ∧
      ∀ p, Function.Injective (mfderiv planeModel threeModel F p) :=
  exists_embedding_of_component_embeddings (EuclideanSpace.single 0 1) (by simp) hcomponent

theorem exists_spherical_embedding_of_component_three_embeddings [CompactSpace M]
    (hcomponent : ∀ c : ConnectedComponents M, ∃ f : componentOpen c → ThreeSpace,
      ContMDiff planeModel threeModel ∞ f ∧ Function.Injective f ∧
      ∀ p, Function.Injective (mfderiv planeModel threeModel f p)) :
    ∃ I : M → Space, ContMDiff planeModel spaceModel ∞ I ∧
      (∀ p, ‖I p‖ = 1) ∧
      (∀ p, Function.Injective (mfderiv planeModel spaceModel I p)) ∧
      Function.Injective I := by
  obtain ⟨F, hF, hFi, hFm⟩ := exists_three_embedding_of_component_embeddings hcomponent
  exact exists_spherical_embedding_of_three_embedding hF hFi hFm

omit [IsManifold planeModel ∞ M] in
theorem componentAssembly_mvfderiv_restrict
    {f : (c : ConnectedComponents M) → componentOpen c → E}
    (hf : ∀ c, ContMDiff planeModel 𝓘(ℝ, E) ∞ (f c))
    (c : ConnectedComponents M) (p : componentOpen c)
    (v : TangentSpace planeModel p) :
    mvfderiv planeModel (componentAssembly f) p.val
        (mfderiv planeModel planeModel (Subtype.val : componentOpen c → M) p v) =
      mvfderiv planeModel (f c) p v := by
  have heq : (componentAssembly f) ∘ (Subtype.val : componentOpen c → M) = f c := by
    funext q
    exact componentAssembly_restrict f c q
  have hchain := mvfderiv_comp p
    ((componentAssembly_contMDiff hf p.val).mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (I := planeModel) (n := ∞) p).mdifferentiableAt (by simp))
  rw [heq] at hchain
  exact (congrArg (fun A => A v) hchain).symm

/-- The component metric condition is the pullback of the *given* global
metric by the open inclusion. No replacement metric or atlas is used. -/
theorem exists_isometric_embedding_of_component_maps [CompactSpace M]
    (g : SmoothMetric M)
    (hcomponent : ∀ c : ConnectedComponents M, ∃ f : componentOpen c → Space,
      ContMDiff planeModel spaceModel ∞ f ∧ Function.Injective f ∧
      ∀ (p : componentOpen c) (v w : TangentSpace planeModel p),
        inner ℝ (mvfderiv planeModel f p v) (mvfderiv planeModel f p w) =
          g.inner p.val
            (mfderiv planeModel planeModel (Subtype.val : componentOpen c → M) p v)
            (mfderiv planeModel planeModel (Subtype.val : componentOpen c → M) p w)) :
    ∃ F : M → Space, IsSmoothIsometricEmbedding g F := by
  classical
  choose f hs hi hm using hcomponent
  obtain ⟨b, hb⟩ := exists_component_translations (fun c => (hs c).continuous)
    (EuclideanSpace.single 0 1) (by simp)
  let translated : (c : ConnectedComponents M) → componentOpen c → Space :=
    fun c p => f c p + b c
  have ht : ∀ c, ContMDiff planeModel spaceModel ∞ (translated c) :=
    fun c => ((contDiff_id.add contDiff_const :
      ContDiff ℝ ∞ (fun x : Space => x + b c)).contMDiff).comp (hs c)
  refine ⟨componentAssembly translated, ⟨componentAssembly_contMDiff ht, ?_⟩, ?_⟩
  · intro p v w
    let c := ConnectedComponents.mk p
    let q : componentOpen c := ⟨p, rfl⟩
    obtain ⟨v', hv'⟩ := openSubtype_mfderiv_surjective (componentOpen c) q v
    obtain ⟨w', hw'⟩ := openSubtype_mfderiv_surjective (componentOpen c) q w
    have hmetric := hm c q v' w'
    have hvcomp := componentAssembly_mvfderiv_restrict ht c q v'
    have hwcomp := componentAssembly_mvfderiv_restrict ht c q w'
    rw [hv', translation_mvfderiv (hs c) (b c) q] at hvcomp
    rw [hw', translation_mvfderiv (hs c) (b c) q] at hwcomp
    rw [hv', hw'] at hmetric
    change inner ℝ (mvfderiv planeModel (componentAssembly translated) p v)
      (mvfderiv planeModel (componentAssembly translated) p w) = g.inner p v w
    exact (congrArg₂ (inner ℝ) hvcomp hwcomp).trans hmetric
  · apply componentAssembly_injective
    · intro c p q heq
      exact hi c (add_right_cancel heq)
    · exact hb

end R4Embedding
