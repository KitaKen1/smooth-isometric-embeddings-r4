import R4Initial.ModelPresentationValid
import R4Initial.ModelFaceMap
import R4Initial.NormalFormGenus
import R4CoS.SphereCarrierGeometry

/-! Stage 07d(B), geometric half, part 2: the polygonal realization of the four-face presentation
is homeomorphic to the polynomial model.

The face `(up, s)` goes into sheet `s` of the double of `D_g` by the upper face map (`up = true`)
or the lower face map. Side `j` of the `(4g+2)`-gon goes to the edge of its dart, the edge being
parametrized by increasing `x` (`sheet_side`), so the two occurrences of an edge have the same
image and the map descends to the realization. It is injective because points with the same image
are glued by the side identifications (`mk_seg`, `mk_cross_point`), surjective because the two face
maps cover the two halves of `D_g`, and a continuous bijection from a compact space onto a
Hausdorff space is a homeomorphism. -/

noncomputable section
namespace R4Embedding
namespace ModelPresentation

open R4CoS.Topology.ClassificationOfSurfaces SurfaceCellComplex FiniteCyclicPresentation
open ModelFace

variable {g : ℕ}

/-! ### Side identifications of a valid presentation -/

/-- Two occurrences of an edge with the same dart glue their sides with the same parameter. -/
theorem polygonalMk_side_same {P : FiniteCyclicPresentation} (valid : P.IsSurfaceValid)
    (o₁ o₂ : P.BoundaryOccurrence) (hne : o₁ ≠ o₂) (hmult : P.edgeMultiplicity o₁.edge = 2)
    (hd : o₂.dart = o₁.dart) (t : unitInterval) :
    P.polygonalMk valid ⟨o₁.1, PolygonCell.side o₁.2 t⟩ =
      P.polygonalMk valid ⟨o₂.1, PolygonCell.side o₂.2 t⟩ := by
  have hedge : o₂.edge = o₁.edge := by
    simp only [BoundaryOccurrence.edge, hd]
  let p : P.BoundaryPairing :=
    { source := o₁
      target := o₂
      source_ne_target := hne
      source_not_boundary := by unfold IsBoundaryEdge; omega
      target_not_boundary := by unfold IsBoundaryEdge; rw [hedge]; omega
      direction := .same
      compatible := hd }
  exact PolygonGluing.mk_source_eq_mk_target p.identification (pairing_identification_mem valid p) t

/-- Two occurrences of an edge with opposite darts glue their sides with reversed parameters. -/
theorem polygonalMk_side_flip {P : FiniteCyclicPresentation} (valid : P.IsSurfaceValid)
    (o₁ o₂ : P.BoundaryOccurrence) (hne : o₁ ≠ o₂) (hmult : P.edgeMultiplicity o₁.edge = 2)
    (hd : o₂.dart = o₁.dart.flip) (t : unitInterval) :
    P.polygonalMk valid ⟨o₁.1, PolygonCell.side o₁.2 t⟩ =
      P.polygonalMk valid ⟨o₂.1, PolygonCell.side o₂.2 (unitInterval.symm t)⟩ := by
  have hedge : o₂.edge = o₁.edge := by
    simp only [BoundaryOccurrence.edge, hd]
    generalize o₁.dart = d
    cases d <;> rfl
  let p : P.BoundaryPairing :=
    { source := o₁
      target := o₂
      source_ne_target := hne
      source_not_boundary := by unfold IsBoundaryEdge; omega
      target_not_boundary := by unfold IsBoundaryEdge; rw [hedge]; omega
      direction := .opposite
      compatible := hd }
  exact PolygonGluing.mk_source_eq_mk_target p.identification (pairing_identification_mem valid p) t

/-! ### Cells and sides of the four-face presentation -/

theorem boundary_length (f : (presentation g).Face) :
    ((presentation g).boundary f).length = 4 * g + 2 := by
  rw [boundary_faceKey, List.length_map, length_faceWord]

theorem side_val (f : (presentation g).Face) (i : Fin ((presentation g).boundary f).length)
    (t : unitInterval) : (PolygonCell.side i t).val = sidePt g i.val t := by
  have hn : ((((presentation g).boundary f).length : ℕ) : ℝ) = 4 * g + 2 := by
    rw [boundary_length]
    push_cast
    ring
  have hθ : PolygonCell.sideAngle i t = Real.pi * ((i.val : ℝ) + t) / (2 * g + 1) := by
    unfold PolygonCell.sideAngle
    rw [hn]
    have h : (2 * (g : ℝ) + 1) ≠ 0 := by positivity
    first | (field_simp; ring) | field_simp
  show ((Circle.exp (PolygonCell.sideAngle i t) : Circle) : ℂ) = _
  rw [Circle.coe_exp, hθ]
  rfl

theorem norm_cell {n : ℕ} (z : PolygonCell n) : ‖z.val‖ ≤ 1 := by
  simpa using z.property

/-- The occurrence at side `j` of a face. -/
def occ (f : (presentation g).Face) (j : ℕ) (hj : j < 4 * g + 2) :
    (presentation g).BoundaryOccurrence :=
  ⟨f, ⟨j, by rw [boundary_length]; exact hj⟩⟩

theorem dart_get (f : (presentation g).Face) (i : Fin ((presentation g).boundary f).length) :
    ((presentation g).boundary f).get i = SignedDart.mapEquiv (εP g)
      (faceDart (faceKey f).1 (faceKey f).2
        ⟨i.val, by have := i.isLt; have := boundary_length f; omega⟩) := by
  rw [List.get_eq_getElem, List.getElem_of_eq (boundary_faceKey f), List.getElem_map]
  simp only [faceWord, List.getElem_ofFn]

theorem occ_dart (f : (presentation g).Face) (j : ℕ) (hj : j < 4 * g + 2) :
    (occ f j hj).dart =
      SignedDart.mapEquiv (εP g) (faceDart (faceKey f).1 (faceKey f).2 ⟨j, hj⟩) :=
  dart_get f _

theorem mk_cell_eq (f : (presentation g).Face)
    (z : PolygonCell ((presentation g).boundary f).length) (j : ℕ) (hj : j < 4 * g + 2)
    (t : unitInterval) (hz : z.val = sidePt g j t) :
    (⟨f, z⟩ : (presentation g).PolygonalPreRealization) =
      ⟨(occ f j hj).1, PolygonCell.side (occ f j hj).2 t⟩ := by
  have h := side_val f ⟨j, by rw [boundary_length]; exact hj⟩ t
  exact congrArg (Sigma.mk f) (PolygonCell.ext (hz.trans h.symm))

theorem exists_face_key (up s : Bool) : ∃ f : (presentation g).Face, faceKey f = (up, s) := by
  cases up <;> cases s
  · exact ⟨face 3, rfl⟩
  · exact ⟨face 1, rfl⟩
  · exact ⟨face 2, rfl⟩
  · exact ⟨face 0, rfl⟩

/-- The typed dart of a dart of the presentation. -/
def typedDart (d : (presentation g).Dart) : SignedDart (MEdge g) :=
  SignedDart.mapEquiv (εP g).symm d

theorem typedDart_mapEquiv (d : SignedDart (MEdge g)) :
    typedDart (SignedDart.mapEquiv (εP g) d) = d := by
  cases d <;> simp [typedDart]

theorem typedDart_flip (d : (presentation g).Dart) : typedDart d.flip = (typedDart d).flip := by
  cases d <;> rfl

/-! ### Darts that do not depend on the sheet -/

theorem faceDart_sheet_upper_outer {j : ℕ} (hj : j ≤ 2 * g) (s s' : Bool)
    (h : j < 4 * g + 2) : faceDart true s ⟨j, h⟩ = faceDart true s' ⟨j, h⟩ := by
  rw [faceDart_tu j (2 * g - j) h (by omega) (by omega),
    faceDart_tu j (2 * g - j) h (by omega) (by omega)]

theorem faceDart_sheet_upper_hole {i : ℕ} (hi : i < g) (s s' : Bool)
    (h : 2 * g + 1 + (2 * i + 1) < 4 * g + 2) :
    faceDart true s ⟨2 * g + 1 + (2 * i + 1), h⟩ = faceDart true s' ⟨2 * g + 1 + (2 * i + 1), h⟩ := by
  rw [faceDart_tl _ (2 * i + 1) h (by omega) rfl, faceDart_tl _ (2 * i + 1) h (by omega) rfl,
    piece_sheet_eq (up := true) (s := s) (s' := s') (2 * i + 1) (by omega) (by omega)]

theorem faceDart_sheet_lower_outer {j : ℕ} (hj : 2 * g + 1 ≤ j) (s s' : Bool)
    (h : j < 4 * g + 2) : faceDart false s ⟨j, h⟩ = faceDart false s' ⟨j, h⟩ := by
  rw [faceDart_fu j (j - (2 * g + 1)) h (by omega) (by omega),
    faceDart_fu j (j - (2 * g + 1)) h (by omega) (by omega)]

theorem faceDart_sheet_lower_hole {i : ℕ} (hi : i < g) (s s' : Bool)
    (h : 2 * g - (2 * i + 1) < 4 * g + 2) :
    faceDart false s ⟨2 * g - (2 * i + 1), h⟩ = faceDart false s' ⟨2 * g - (2 * i + 1), h⟩ := by
  rw [faceDart_fl _ (2 * i + 1) h (by omega) (by omega),
    faceDart_fl _ (2 * i + 1) h (by omega) (by omega),
    piece_sheet_eq (up := false) (s := s) (s' := s') (2 * i + 1) (by omega) (by omega)]

theorem faceDart_sheet_lower_hole' {i : ℕ} (hi : i < g) {j : ℕ} (hj : j = 2 * g - (2 * i + 1))
    (s s' : Bool) (h : j < 4 * g + 2) : faceDart false s ⟨j, h⟩ = faceDart false s' ⟨j, h⟩ := by
  subst hj
  exact faceDart_sheet_lower_hole hi s s' h

/-! ### The map to the double -/

/-- Inclusion of a sheet into the double. -/
def sheetMk (s : Bool) (q : PlanarModelDomain g) : ModelDouble g :=
  Quotient.mk _ (if s then Sum.inl q else Sum.inr q)

theorem sheetMk_eq_iff (s s' : Bool) (q q' : PlanarModelDomain g) :
    sheetMk s q = sheetMk s' q' ↔ q = q' ∧ (s = s' ∨ modelPlanarProduct g q.1 = 0) := by
  unfold sheetMk
  rw [Quotient.eq]
  cases s <;> cases s' <;> exact Iff.rfl

theorem sheetMk_cross (s s' : Bool) (q : PlanarModelDomain g)
    (hq : modelPlanarProduct g q.1 = 0) : sheetMk s q = sheetMk s' q :=
  (sheetMk_eq_iff s s' q q).mpr ⟨rfl, Or.inr hq⟩

theorem continuous_sheetMk (s : Bool) : Continuous (sheetMk (g := g) s) := by
  cases s
  · exact continuous_quotient_mk'.comp continuous_inr
  · exact continuous_quotient_mk'.comp continuous_inl

/-- The point of the planar model given by a face point. -/
def halfPt (up : Bool) (z : ℂ) (hz : ‖z‖ ≤ 1) : PlanarModelDomain g :=
  if up then ⟨facePt g z, (facePt_mem g hz).1⟩ else ⟨facePtLow g z, (facePtLow_mem g hz).1⟩

theorem halfPt_val (up : Bool) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    (halfPt (g := g) up z hz).1 = if up then facePt g z else facePtLow g z := by
  cases up <;> rfl

theorem halfPt_congr {up : Bool} {z z' : ℂ} (h : z = z') (hz : ‖z‖ ≤ 1) (hz' : ‖z'‖ ≤ 1) :
    halfPt (g := g) up z hz = halfPt up z' hz' := by
  subst h
  rfl

theorem continuous_halfPt_cell (up : Bool) (n : ℕ) :
    Continuous fun z : PolygonCell n => halfPt (g := g) up z.val (norm_cell z) := by
  cases up
  · exact ((continuousOn_facePtLow g).comp_continuous PolygonCell.continuous_val
      fun z => z.property).subtype_mk _
  · exact ((continuousOn_facePt g).comp_continuous PolygonCell.continuous_val
      fun z => z.property).subtype_mk _

/-- The map from the disjoint union of the face polygons to the double. -/
def preMap (x : (presentation g).PolygonalPreRealization) : ModelDouble g :=
  sheetMk (faceKey x.1).2 (halfPt (faceKey x.1).1 x.2.val (norm_cell x.2))

theorem continuous_preMap : Continuous (preMap (g := g)) :=
  continuous_sigma fun f =>
    (continuous_sheetMk (faceKey f).2).comp (continuous_halfPt_cell (faceKey f).1 _)

/-- The standard parametrization of each edge, by increasing `x`. -/
def edgeMap : MEdge g → unitInterval → ModelDouble g
  | .seg s j, t =>
      sheetMk s (halfPt true (sidePt g (2 * g + 1 + 2 * j.val) t) (norm_sidePt g _ _).le)
  | .hole true i, t =>
      sheetMk true (halfPt true (sidePt g (2 * g + 1 + (2 * i.val + 1)) t) (norm_sidePt g _ _).le)
  | .hole false i, t =>
      sheetMk true (halfPt false (sidePt g (2 * g - (2 * i.val + 1)) (1 - t)) (norm_sidePt g _ _).le)
  | .outer true k, t =>
      sheetMk true (halfPt true (sidePt g (2 * g - k.val) (1 - t)) (norm_sidePt g _ _).le)
  | .outer false k, t =>
      sheetMk true (halfPt false (sidePt g (2 * g + 1 + k.val) t) (norm_sidePt g _ _).le)

/-- The image of a parameter on a dart. -/
def dartMap : SignedDart (MEdge g) → unitInterval → ModelDouble g
  | .pos e, t => edgeMap e t
  | .neg e, t => edgeMap e (unitInterval.symm t)

theorem dartMap_flip (d : SignedDart (MEdge g)) (t : unitInterval) :
    dartMap d.flip (unitInterval.symm t) = dartMap d t := by
  cases d with
  | pos e =>
    show edgeMap e (unitInterval.symm (unitInterval.symm t)) = edgeMap e t
    rw [unitInterval.symm_symm]
  | neg e => rfl

theorem facePtLow_sidePt {j : ℕ} (hj : j ≤ 4 * g + 1) (t : ℝ) :
    facePtLow g (sidePt g j t) = reflect (facePt g (sidePt g (4 * g + 1 - j) (1 - t))) := by
  rw [facePtLow, conj_sidePt g hj]

/-- Side `j` of the face `(up, s)` goes to the edge of its dart. -/
theorem sheet_side (up s : Bool) (j : ℕ) (hj : j < 4 * g + 2) (t : unitInterval) :
    sheetMk s (halfPt up (sidePt g j t) (norm_sidePt g _ _).le) =
      dartMap (faceDart up s ⟨j, hj⟩) t := by
  have ht₀ : (0 : ℝ) ≤ t := t.2.1
  have ht₁ : (t : ℝ) ≤ 1 := t.2.2
  have hσ : (1 : ℝ) - (unitInterval.symm t : ℝ) = t := by
    rw [unitInterval.coe_symm_eq]
    ring
  by_cases hle : j ≤ 2 * g
  · cases up
    · rw [faceDart_fl j (2 * g - j) hj (by omega) (by omega)]
      rcases Nat.mod_two_eq_zero_or_one (2 * g - j) with hk | hk
      · -- a segment of sheet `s`
        rw [piece_of_even (by simpa using hk)]
        show _ = sheetMk s (halfPt true
          (sidePt g (2 * g + 1 + 2 * ((2 * g - j) / 2)) (unitInterval.symm t)) _)
        congr 1
        apply Subtype.ext
        rw [halfPt_val, halfPt_val, if_neg Bool.false_ne_true, if_pos rfl,
          facePtLow_sidePt (j := j) (by omega)]
        have hj' : 4 * g + 1 - j = 2 * g + 1 + 2 * ((2 * g - j) / 2) := by omega
        rw [hj', ← unitInterval.coe_symm_eq]
        exact reflect_of_one_eq_zero (by
          rw [facePt_one]
          exact faceY_seg_side g (by omega) (unitInterval.symm t).2.1 (unitInterval.symm t).2.2)
      · -- a lower hole semicircle
        rw [piece_of_odd (by simpa using hk)]
        show _ = sheetMk true (halfPt false
          (sidePt g (2 * g - (2 * ((2 * g - j) / 2) + 1)) (1 - (unitInterval.symm t : ℝ))) _)
        rw [halfPt_congr (show sidePt g (2 * g - (2 * ((2 * g - j) / 2) + 1))
            (1 - (unitInterval.symm t : ℝ)) = sidePt g j t by rw [hσ]; congr 1; omega)
          _ (norm_sidePt g _ _).le]
        apply sheetMk_cross
        rw [halfPt_val, if_neg Bool.false_ne_true, facePtLow_sidePt (j := j) (by omega), product_reflect]
        have hj' : 4 * g + 1 - j = 2 * g + 1 + (2 * ((2 * g - j) / 2) + 1) := by omega
        rw [hj', ← unitInterval.coe_symm_eq]
        exact product_hole_side g (by omega) (unitInterval.symm t).2.1 (unitInterval.symm t).2.2
    · -- an upper outer piece
      rw [faceDart_tu j (2 * g - j) hj (by omega) (by omega)]
      show _ = sheetMk true (halfPt true
        (sidePt g (2 * g - (2 * g - j)) (1 - (unitInterval.symm t : ℝ))) _)
      rw [halfPt_congr (show sidePt g (2 * g - (2 * g - j)) (1 - (unitInterval.symm t : ℝ)) =
          sidePt g j t by rw [hσ]; congr 1; omega) _ (norm_sidePt g _ _).le]
      apply sheetMk_cross
      rw [halfPt_val, if_pos rfl]
      exact product_upper_side g hle ht₀ ht₁
  · cases up
    · -- a lower outer piece
      rw [faceDart_fu j (j - (2 * g + 1)) hj (by omega) (by omega)]
      show _ = sheetMk true (halfPt false (sidePt g (2 * g + 1 + (j - (2 * g + 1))) t) _)
      rw [halfPt_congr (show sidePt g (2 * g + 1 + (j - (2 * g + 1))) t = sidePt g j t by
          congr 1; omega) _ (norm_sidePt g _ _).le]
      apply sheetMk_cross
      rw [halfPt_val, if_neg Bool.false_ne_true, facePtLow_sidePt (j := j) (by omega), product_reflect]
      exact product_upper_side g (by omega) (by linarith) (by linarith)
    · rw [faceDart_tl j (j - (2 * g + 1)) hj (by omega) (by omega)]
      rcases Nat.mod_two_eq_zero_or_one (j - (2 * g + 1)) with hk | hk
      · -- a segment of sheet `s`
        rw [piece_of_even (by simpa using hk)]
        show _ = sheetMk s (halfPt true
          (sidePt g (2 * g + 1 + 2 * ((j - (2 * g + 1)) / 2)) t) _)
        rw [halfPt_congr (show sidePt g (2 * g + 1 + 2 * ((j - (2 * g + 1)) / 2)) t =
            sidePt g j t by congr 1; omega) _ (norm_sidePt g _ _).le]
      · -- an upper hole semicircle
        rw [piece_of_odd (by simpa using hk)]
        show _ = sheetMk true (halfPt true
          (sidePt g (2 * g + 1 + (2 * ((j - (2 * g + 1)) / 2) + 1)) t) _)
        rw [halfPt_congr (show sidePt g (2 * g + 1 + (2 * ((j - (2 * g + 1)) / 2) + 1)) t =
            sidePt g j t by congr 1; omega) _ (norm_sidePt g _ _).le]
        apply sheetMk_cross
        rw [halfPt_val, if_pos rfl]
        have hj' : j = 2 * g + 1 + (2 * ((j - (2 * g + 1)) / 2) + 1) := by omega
        rw [hj']
        exact product_hole_side g (by omega) ht₀ ht₁

theorem preMap_side (f : (presentation g).Face) (i : Fin ((presentation g).boundary f).length)
    (t : unitInterval) :
    preMap ⟨f, PolygonCell.side i t⟩ = dartMap (typedDart (((presentation g).boundary f).get i)) t := by
  have hi : i.val < 4 * g + 2 := by
    have := i.isLt
    have := boundary_length f
    omega
  rw [dart_get, typedDart_mapEquiv, ← sheet_side (faceKey f).1 (faceKey f).2 i.val hi t]
  unfold preMap
  exact congrArg _ (halfPt_congr (side_val f i t) _ _)

/-! ### The map from the realization -/

theorem preMap_generator {x y : (presentation g).PolygonalPreRealization}
    (h : PolygonGluing.Generator
      ((presentation g).polygonalIdentifications isSurfaceValid_presentation) x y) :
    preMap x = preMap y := by
  cases h with
  | glue idf hmem t =>
    obtain ⟨p, rfl⟩ := hmem
    rcases p with ⟨o₁, o₂, hne, hb₁, hb₂, d, hc⟩
    show preMap ⟨o₁.1, PolygonCell.side o₁.2 t⟩ =
      preMap ⟨o₂.1, PolygonCell.side o₂.2 (d.homeomorph t)⟩
    rw [preMap_side, preMap_side]
    cases d with
    | same =>
      have hc' : o₂.dart = o₁.dart := hc
      show dartMap (typedDart o₁.dart) t = dartMap (typedDart o₂.dart) t
      rw [hc']
    | opposite =>
      have hc' : o₂.dart = o₁.dart.flip := hc
      show dartMap (typedDart o₁.dart) t = dartMap (typedDart o₂.dart) (unitInterval.symm t)
      rw [hc', typedDart_flip, dartMap_flip]

theorem preMap_respects (a b : (presentation g).PolygonalPreRealization)
    (h : Relation.EqvGen (PolygonGluing.Generator
      ((presentation g).polygonalIdentifications isSurfaceValid_presentation)) a b) :
    preMap a = preMap b := by
  induction h with
  | rel x y hxy => exact preMap_generator hxy
  | refl => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The map from the realization to the double. -/
def realMap : (presentation g).PolygonalRealization isSurfaceValid_presentation → ModelDouble g :=
  Quotient.lift preMap fun a b h => preMap_respects a b h

theorem continuous_realMap : Continuous (realMap (g := g)) :=
  continuous_preMap.quotient_lift _

theorem realMap_surjective : Function.Surjective (realMap (g := g)) := by
  intro x
  induction x using Quotient.ind with
  | _ a =>
    obtain ⟨s, q, hsq⟩ : ∃ s q, sheetMk s q = Quotient.mk _ a := by
      rcases a with q | q
      · exact ⟨true, q, rfl⟩
      · exact ⟨false, q, rfl⟩
    rw [← hsq]
    rcases le_total 0 (q.1 1) with hq | hq
    · obtain ⟨z, hz, hzq⟩ := exists_facePt g q.2 hq
      obtain ⟨f, hf⟩ := exists_face_key (g := g) true s
      refine ⟨Quotient.mk _ ⟨f, ⟨z, by simpa using hz⟩⟩, ?_⟩
      show preMap ⟨f, ⟨z, _⟩⟩ = sheetMk s q
      unfold preMap
      rw [hf]
      exact congrArg (sheetMk s) (Subtype.ext hzq)
    · obtain ⟨z, hz, hzq⟩ := exists_facePtLow g q.2 hq
      obtain ⟨f, hf⟩ := exists_face_key (g := g) false s
      refine ⟨Quotient.mk _ ⟨f, ⟨z, by simpa using hz⟩⟩, ?_⟩
      show preMap ⟨f, ⟨z, _⟩⟩ = sheetMk s q
      unfold preMap
      rw [hf]
      exact congrArg (sheetMk s) (Subtype.ext hzq)

/-! ### Injectivity -/

/-- The quotient map onto the realization. -/
abbrev mkR (x : (presentation g).PolygonalPreRealization) :
    (presentation g).PolygonalRealization isSurfaceValid_presentation :=
  (presentation g).polygonalMk isSurfaceValid_presentation x

/-- The two halves of a sheet are glued along the segments of the `x`-axis. -/
theorem mk_seg (s : Bool) {fT fF : (presentation g).Face} (hT : faceKey fT = (true, s))
    (hF : faceKey fF = (false, s)) {j₀ : ℕ} (hj₀ : j₀ ≤ g) (t : unitInterval) :
    mkR ⟨(occ fT (2 * g + 1 + 2 * j₀) (by omega)).1,
        PolygonCell.side (occ fT (2 * g + 1 + 2 * j₀) (by omega)).2 t⟩ =
      mkR ⟨(occ fF (2 * g - 2 * j₀) (by omega)).1,
        PolygonCell.side (occ fF (2 * g - 2 * j₀) (by omega)).2 (unitInterval.symm t)⟩ := by
  apply polygonalMk_side_flip isSurfaceValid_presentation
  · intro h
    have h1 : fT = fF := congrArg Sigma.fst h
    rw [h1, hF] at hT
    simp at hT
  · exact edgeMultiplicity_presentation _
  · rw [occ_dart, occ_dart, hT, hF]
    dsimp only
    rw [faceDart_fl (2 * g - 2 * j₀) (2 * j₀) _ (by omega) (by omega),
      faceDart_tl (2 * g + 1 + 2 * j₀) (2 * j₀) _ (by omega) rfl,
      piece_up_eq (up := false) (up' := true) (s := s) (2 * j₀) (by omega) (by omega)]
    rfl

/-- Two cells of the same half in the two sheets are glued at a common point of a boundary
circle. -/
theorem mk_cross_point {f f' : (presentation g).Face} {up : Bool} (hf : (faceKey f).1 = up)
    (hf' : (faceKey f').1 = up) (z : PolygonCell ((presentation g).boundary f).length)
    (z' : PolygonCell ((presentation g).boundary f').length) (hzz : z.val = z'.val)
    (hs : (faceKey f).2 = (faceKey f').2 ∨
      modelPlanarProduct g (if up then facePt g z.val else facePtLow g z.val) = 0) :
    mkR ⟨f, z⟩ = mkR ⟨f', z'⟩ := by
  by_cases hff : f = f'
  · subst hff
    rw [PolygonCell.ext hzz]
  · have hprod : modelPlanarProduct g (if up then facePt g z.val else facePtLow g z.val) = 0 :=
      hs.resolve_left fun h2 => hff (faceKey_injective (Prod.ext (hf.trans hf'.symm) h2))
    have hne : ∀ (j : ℕ) (hj : j < 4 * g + 2), occ f j hj ≠ occ f' j hj :=
      fun _ _ h => hff (congrArg Sigma.fst h)
    cases up
    · rw [if_neg Bool.false_ne_true, facePtLow, product_reflect] at hprod
      have hzc : ‖starRingEnd ℂ z.val‖ ≤ 1 := by rw [Complex.norm_conj]; exact norm_cell z
      obtain ⟨j, t, ht₀, ht₁, hzt, hj⟩ := exists_boundary_side g hzc hprod
      have hjlt : j ≤ 4 * g + 1 := by rcases hj with hj | ⟨i, hi, rfl⟩ <;> omega
      have hzv : z.val = sidePt g (4 * g + 1 - j) ((unitInterval.symm ⟨t, ht₀, ht₁⟩ : unitInterval) : ℝ) := by
        rw [unitInterval.coe_symm_eq, ← conj_sidePt g hjlt, ← hzt]
        simp
      rw [mk_cell_eq f z (4 * g + 1 - j) (by omega) _ hzv,
        mk_cell_eq f' z' (4 * g + 1 - j) (by omega) _ (hzz ▸ hzv)]
      apply polygonalMk_side_same isSurfaceValid_presentation _ _ (hne _ _)
        (edgeMultiplicity_presentation _)
      rw [occ_dart, occ_dart, hf, hf']
      congr 1
      rcases hj with hj | ⟨i, hi, rfl⟩
      · exact faceDart_sheet_lower_outer (by omega) _ _ _
      · exact faceDart_sheet_lower_hole' hi (by omega) _ _ _
    · rw [if_pos rfl] at hprod
      obtain ⟨j, t, ht₀, ht₁, hzt, hj⟩ := exists_boundary_side g (norm_cell z) hprod
      have hjlt : j < 4 * g + 2 := by rcases hj with hj | ⟨i, hi, rfl⟩ <;> omega
      rw [mk_cell_eq f z j hjlt ⟨t, ht₀, ht₁⟩ hzt, mk_cell_eq f' z' j hjlt ⟨t, ht₀, ht₁⟩ (hzz ▸ hzt)]
      apply polygonalMk_side_same isSurfaceValid_presentation _ _ (hne _ _)
        (edgeMultiplicity_presentation _)
      rw [occ_dart, occ_dart, hf, hf']
      congr 1
      rcases hj with hj | ⟨i, hi, rfl⟩
      · exact faceDart_sheet_upper_outer hj _ _ _
      · exact faceDart_sheet_upper_hole hi _ _ _

/-- A point of an upper cell and a point of a lower cell with the same image are glued. -/
theorem mk_upper_lower {f f' : (presentation g).Face}
    (z : PolygonCell ((presentation g).boundary f).length)
    (z' : PolygonCell ((presentation g).boundary f').length) {s s' : Bool}
    (hk : faceKey f = (true, s)) (hk' : faceKey f' = (false, s'))
    (hq : facePt g z.val = facePtLow g z'.val)
    (hs : s = s' ∨ modelPlanarProduct g (facePt g z.val) = 0) :
    mkR ⟨f, z⟩ = mkR ⟨f', z'⟩ := by
  obtain ⟨hzz, hy⟩ := facePt_eq_facePtLow g (norm_cell z) (norm_cell z') hq
  obtain ⟨j₀, hj₀, t, ht₀, ht₁, hzt⟩ := exists_seg_side g (norm_cell z) hy
  obtain ⟨fF, hfF⟩ := exists_face_key (g := g) false s
  have hz'v : z'.val = sidePt g (2 * g - 2 * j₀)
      ((unitInterval.symm ⟨t, ht₀, ht₁⟩ : unitInterval) : ℝ) := by
    rw [hzz, hzt, conj_sidePt g (j := 2 * g + 1 + 2 * j₀) (by omega), unitInterval.coe_symm_eq,
      show 4 * g + 1 - (2 * g + 1 + 2 * j₀) = 2 * g - 2 * j₀ by omega]
  rw [mk_cell_eq f z (2 * g + 1 + 2 * j₀) (by omega) ⟨t, ht₀, ht₁⟩ hzt, mk_seg s hk hfF hj₀]
  let w : PolygonCell ((presentation g).boundary fF).length :=
    PolygonCell.side (occ fF (2 * g - 2 * j₀) (by omega)).2 (unitInterval.symm ⟨t, ht₀, ht₁⟩)
  have hw : w.val = z'.val := by
    rw [hz'v]
    exact side_val fF _ _
  show mkR ⟨fF, w⟩ = mkR ⟨f', z'⟩
  refine mk_cross_point (up := false) (by rw [hfF]) (by rw [hk']) w z' hw ?_
  rw [hfF, hk', if_neg Bool.false_ne_true, hw, ← hq]
  rcases hs with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr h

theorem mk_eq_of_preMap_eq {a b : (presentation g).PolygonalPreRealization}
    (h : preMap a = preMap b) : mkR a = mkR b := by
  obtain ⟨f, z⟩ := a
  obtain ⟨f', z'⟩ := b
  obtain ⟨hq, hs⟩ := (sheetMk_eq_iff _ _ _ _).mp h
  have hq1 := congrArg Subtype.val hq
  simp only [halfPt_val] at hq1 hs
  rcases hk : faceKey f with ⟨up, s⟩
  rcases hk' : faceKey f' with ⟨up', s'⟩
  simp only [hk, hk'] at hq1 hs
  cases up <;> cases up'
  · -- both lower
    simp only [Bool.false_eq_true, ↓reduceIte] at hq1 hs
    have hzz : z.val = z'.val := facePtLow_injOn g (by simpa using norm_cell z)
      (by simpa using norm_cell z') hq1
    exact mk_cross_point (up := false) (by rw [hk]) (by rw [hk']) z z' hzz
      (by rw [hk, hk']; simpa using hs)
  · -- lower, upper
    simp only [Bool.false_eq_true, ↓reduceIte] at hq1 hs
    refine (mk_upper_lower z' z hk' hk hq1.symm ?_).symm
    rcases hs with h | h
    · exact Or.inl h.symm
    · rw [← hq1]
      exact Or.inr h
  · -- upper, lower
    simp only [Bool.false_eq_true, ↓reduceIte] at hq1 hs
    exact mk_upper_lower z z' hk hk' hq1 hs
  · -- both upper
    simp only [↓reduceIte] at hq1 hs
    have hzz : z.val = z'.val := facePt_injOn g (by simpa using norm_cell z)
      (by simpa using norm_cell z') hq1
    exact mk_cross_point (up := true) (by rw [hk]) (by rw [hk']) z z' hzz
      (by rw [hk, hk']; simpa using hs)

theorem realMap_injective : Function.Injective (realMap (g := g)) := by
  intro x y
  refine Quotient.inductionOn₂ x y fun a b hab => ?_
  exact mk_eq_of_preMap_eq (a := a) (b := b) hab

/-! ### The homeomorphism -/

/-- The realization of the four-face presentation is the polynomial model. -/
def realHomeomorph (g : ℕ) :
    (presentation g).PolygonalRealization isSurfaceValid_presentation ≃ₜ PolynomialLevel g :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (fun x => modelDoubleHomeomorph g (realMap x))
      ⟨(modelDoubleHomeomorph g).injective.comp realMap_injective,
        (modelDoubleHomeomorph g).surjective.comp realMap_surjective⟩)
    ((modelDoubleHomeomorph g).continuous.comp continuous_realMap)

/-- The polynomial model of genus `g` has a polygonal presentation with `χ = 2 − 2g`. -/
def polynomialPresentation (g : ℕ) : PolynomialPresentation g where
  presentation := presentation g
  valid := isSurfaceValid_presentation
  connected := isConnected_presentation
  euler := eulerChar_presentation
  realization := ⟨realHomeomorph g⟩

end ModelPresentation

/-- Stage 07d: the closed orientable normal forms are the polynomial models, given the two
exclusion statements and the orientability of the polynomial levels. -/
theorem orientableNormalFormModelStatement_of_exclusions
    (hnon : NoNonOrientableNormalFormStatement.{0})
    (horient : PolynomialLevelOrientableStatement) : OrientableNormalFormModelStatement :=
  orientableNormalFormModelStatement_of_presentations noBoundaryNormalFormStatement_holds hnon
    horient fun g _ => ⟨ModelPresentation.polynomialPresentation g⟩

end R4Embedding
