import R4Embedding.PolynomialRegion
import R4Embedding.PolynomialLevelAtlas
import Mathlib.Topology.Homeomorph.Lemmas

/-! The two copies of the actual disk with holes are identified only at
their common circle locus. The resulting quotient is homeomorphic to the
actual polynomial zero level. This is a topological gluing theorem; it does
not assert genus or smooth classification of an arbitrary supplied atlas. -/

set_option autoImplicit false
noncomputable section
namespace R4Embedding

open Set

theorem planarModelDomain_compactSpace (g : ℕ) : CompactSpace (PlanarModelDomain g) := by
  let _ : CompactSpace (ModelUpperHalf g) := isCompact_iff_compactSpace.mp
    ((modelPolynomial_level_compact g).inter_right
      (isClosed_le continuous_const (continuous_apply (2 : Fin 3))))
  exact (modelUpperHomeomorph g).symm.compactSpace

abbrev ModelDoubleSource (g : ℕ) := PlanarModelDomain g ⊕ PlanarModelDomain g

def modelDoubleBase {g : ℕ} : ModelDoubleSource g → PlanarModelDomain g := Sum.elim id id
def modelDoubleSide {g : ℕ} : ModelDoubleSource g → Bool := Sum.elim (fun _ => true) (fun _ => false)

def modelDoubleSetoid (g : ℕ) : Setoid (ModelDoubleSource g) where
  r a b := modelDoubleBase a = modelDoubleBase b ∧
    (modelDoubleSide a = modelDoubleSide b ∨ modelPlanarProduct g (modelDoubleBase a) = 0)
  iseqv :=
    { refl := fun _ => ⟨rfl, Or.inl rfl⟩
      symm := by
        rintro a b ⟨hab, hs | hz⟩
        · exact ⟨hab.symm, Or.inl hs.symm⟩
        · refine ⟨hab.symm, Or.inr ?_⟩
          rw [← hab]
          exact hz
      trans := by
        rintro a b c ⟨hab, hs | hz⟩ ⟨hbc, ht | hw⟩
        · exact ⟨hab.trans hbc, Or.inl (hs.trans ht)⟩
        · refine ⟨hab.trans hbc, Or.inr ?_⟩
          rw [hab]
          exact hw
        · exact ⟨hab.trans hbc, Or.inr hz⟩
        · exact ⟨hab.trans hbc, Or.inr hz⟩ }

abbrev ModelDouble (g : ℕ) := Quotient (modelDoubleSetoid g)

def modelDoubleGraph (g : ℕ) : ModelDoubleSource g → PolynomialLevel g :=
  Sum.elim
    (fun q => ⟨modelUpperPoint g q, modelUpperPoint_zero g q.2⟩)
    (fun q => ⟨modelLowerPoint g q, modelLowerPoint_zero g q.2⟩)

theorem modelDoubleGraph_projection (g : ℕ) (a : ModelDoubleSource g) :
    modelPlanarProjection (modelDoubleGraph g a) = (modelDoubleBase a : ModelBase) := by
  cases a <;> exact modelPlanarProjection_heightPoint _ _

theorem modelDoubleGraph_eq_iff (g : ℕ) (a b : ModelDoubleSource g) :
    modelDoubleGraph g a = modelDoubleGraph g b ↔ (modelDoubleSetoid g).r a b := by
  constructor
  · intro h
    have hb : modelDoubleBase a = modelDoubleBase b := Subtype.ext (by
      simpa only [modelDoubleGraph_projection] using
        congrArg (fun p : PolynomialLevel g => modelPlanarProjection p) h)
    refine ⟨hb, ?_⟩
    cases a with
    | inl q =>
      cases b with
      | inl r => exact Or.inl rfl
      | inr r =>
        change q = r at hb
        subst r
        exact Or.inr ((modelUpperPoint_eq_lowerPoint_iff g q.2).mp
          (congrArg Subtype.val h))
    | inr q =>
      cases b with
      | inl r =>
        change q = r at hb
        subst r
        exact Or.inr ((modelUpperPoint_eq_lowerPoint_iff g q.2).mp
          (congrArg Subtype.val h).symm)
      | inr r => exact Or.inl rfl
  · rintro ⟨hb, hs | hz⟩
    · cases a with
      | inl q =>
        cases b with
        | inl r => exact congrArg (modelDoubleGraph g ∘ Sum.inl) hb
        | inr r => cases hs
      | inr q =>
        cases b with
        | inl r => cases hs
        | inr r => exact congrArg (modelDoubleGraph g ∘ Sum.inr) hb
    · cases a with
      | inl q =>
        cases b with
        | inl r => exact congrArg (modelDoubleGraph g ∘ Sum.inl) hb
        | inr r =>
          change q = r at hb
          subst r
          exact Subtype.ext ((modelUpperPoint_eq_lowerPoint_iff g q.2).mpr hz)
      | inr q =>
        cases b with
        | inl r =>
          change q = r at hb
          subst r
          exact Subtype.ext (((modelUpperPoint_eq_lowerPoint_iff g q.2).mpr hz).symm)
        | inr r => exact congrArg (modelDoubleGraph g ∘ Sum.inr) hb

theorem modelDoubleGraph_continuous (g : ℕ) : Continuous (modelDoubleGraph g) := by
  apply continuous_sum_dom.mpr
  exact ⟨((continuous_modelUpperPoint g).comp continuous_subtype_val).subtype_mk _,
    ((continuous_modelLowerPoint g).comp continuous_subtype_val).subtype_mk _⟩

theorem modelDoubleGraph_surjective (g : ℕ) : Function.Surjective (modelDoubleGraph g) := by
  intro p
  let q : PlanarModelDomain g := ⟨modelPlanarProjection p,
    modelPolynomial_zero_projection_region g p.2⟩
  rcases le_total 0 (p.val 2) with hz | hz
  · exact ⟨Sum.inl q, Subtype.ext (modelUpperPoint_recover g p.2 hz)⟩
  · exact ⟨Sum.inr q, Subtype.ext (modelLowerPoint_recover g p.2 hz)⟩

def modelDoubleToLevel (g : ℕ) : ModelDouble g → PolynomialLevel g :=
  Quotient.lift (modelDoubleGraph g) (fun a b h => (modelDoubleGraph_eq_iff g a b).mpr h)

theorem modelDoubleToLevel_continuous (g : ℕ) : Continuous (modelDoubleToLevel g) :=
  (modelDoubleGraph_continuous g).quotient_lift _

theorem modelDoubleToLevel_injective (g : ℕ) : Function.Injective (modelDoubleToLevel g) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro x y h
  exact Quotient.sound ((modelDoubleGraph_eq_iff g x y).mp h)

theorem modelDoubleToLevel_surjective (g : ℕ) : Function.Surjective (modelDoubleToLevel g) := by
  intro p
  obtain ⟨a, ha⟩ := modelDoubleGraph_surjective g p
  exact ⟨Quotient.mk _ a, ha⟩

def modelDoubleHomeomorph (g : ℕ) : ModelDouble g ≃ₜ PolynomialLevel g := by
  let _ := planarModelDomain_compactSpace g
  let e := Equiv.ofBijective (modelDoubleToLevel g)
    ⟨modelDoubleToLevel_injective g, modelDoubleToLevel_surjective g⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := e) (modelDoubleToLevel_continuous g)

theorem modelDoubleHomeomorph_upper (g : ℕ) (q : PlanarModelDomain g) :
    (modelDoubleHomeomorph g (Quotient.mk _ (Sum.inl q))).val = modelUpperPoint g q := rfl

theorem modelDoubleHomeomorph_lower (g : ℕ) (q : PlanarModelDomain g) :
    (modelDoubleHomeomorph g (Quotient.mk _ (Sum.inr q))).val = modelLowerPoint g q := rfl

theorem modelDouble_glue_iff (g : ℕ) (q r : PlanarModelDomain g) :
    (Quotient.mk (modelDoubleSetoid g) (Sum.inl q) : ModelDouble g) =
      Quotient.mk (modelDoubleSetoid g) (Sum.inr r) ↔
        q = r ∧ modelPlanarProduct g q = 0 := by
  rw [Quotient.eq]
  change (q = r ∧ (true = false ∨ modelPlanarProduct g q = 0)) ↔ _
  constructor
  · rintro ⟨hq, h | h⟩
    · cases h
    · exact ⟨hq, h⟩
  · rintro ⟨hq, h⟩
    exact ⟨hq, Or.inr h⟩

theorem modelDouble_glue_iff_circles (g : ℕ) (q : PlanarModelDomain g) :
    (Quotient.mk (modelDoubleSetoid g) (Sum.inl q) : ModelDouble g) =
      Quotient.mk (modelDoubleSetoid g) (Sum.inr q) ↔
        ∃ i ∈ Finset.range (g + 1), modelFactor g i (modelHeightPoint q 0) = 0 := by
  rw [modelDouble_glue_iff]
  simp only [true_and, modelPlanarProduct_zero_iff_circles]

theorem exists_modelDoubleHomeomorph (g : ℕ) :
    Nonempty (ModelDouble g ≃ₜ PolynomialLevel g) := ⟨modelDoubleHomeomorph g⟩

end R4Embedding
