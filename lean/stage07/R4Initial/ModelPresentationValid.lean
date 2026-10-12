import R4Initial.ModelPresentation

/-! Stage 07d(B), combinatorial half (continued): the four-face presentation of the double of the
planar model is surface-valid and connected, and its Euler characteristic is `2 − 2g`. -/

namespace R4Embedding
namespace ModelPresentation

open R4CoS.Topology.ClassificationOfSurfaces SurfaceCellComplex FiniteCyclicPresentation

variable {g : ℕ}

/-! ### Counting edges and faces -/

/-- The edges, sorted by kind. -/
def edgeEquiv : MEdge g ≃ (Bool × Fin (g + 1)) ⊕ (Bool × Fin g) ⊕ (Bool × Fin (2 * g + 1)) where
  toFun
    | .seg s j => .inl (s, j)
    | .hole up i => .inr (.inl (up, i))
    | .outer up k => .inr (.inr (up, k))
  invFun
    | .inl (s, j) => .seg s j
    | .inr (.inl (up, i)) => .hole up i
    | .inr (.inr (up, k)) => .outer up k
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨s, j⟩ | ⟨up, i⟩ | ⟨up, k⟩ <;> rfl

theorem card_edge : Fintype.card (MEdge g) = 8 * g + 4 := by
  rw [Fintype.card_congr edgeEquiv]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  ring

theorem faces_length : (presentation g).faces.length = 4 := rfl

/-- The enumeration of the edges, with its codomain written as the presentation's edges. -/
noncomputable def εP (g : ℕ) : MEdge g ≃ (presentation g).Edge := Fintype.equivFin (MEdge g)

theorem faces_eq :
    (presentation g).faces = (typedFaces g).map (List.map (SignedDart.mapEquiv (εP g))) :=
  rfl

/-- The half sheet of a face of the presentation. -/
def faceKey (f : (presentation g).Face) : Bool × Bool :=
  match f.val with
  | 0 => (true, true)
  | 1 => (false, true)
  | 2 => (true, false)
  | _ => (false, false)

theorem boundary_faceKey (f : (presentation g).Face) :
    (presentation g).boundary f =
      (faceWord (faceKey f).1 (faceKey f).2).map (SignedDart.mapEquiv (εP g)) := by
  obtain ⟨k, hk⟩ := f
  have hk4 : k < 4 := hk
  interval_cases k <;> rfl

theorem faceKey_injective : Function.Injective (faceKey (g := g)) := by
  rintro ⟨k, hk⟩ ⟨k', hk'⟩ h
  have hk4 : k < 4 := hk
  have hk4' : k' < 4 := hk'
  interval_cases k <;> interval_cases k' <;> first | rfl | (simp [faceKey] at h)

theorem boundary_ne_nil (f : (presentation g).Face) : (presentation g).boundary f ≠ [] := by
  intro hnil
  have h := congrArg List.length hnil
  rw [boundary_faceKey, List.length_map, length_faceWord] at h
  simp at h

theorem emptyFaceCount_presentation : emptyFaceCount (presentation g) = 0 := by
  rw [emptyFaceCount, Nat.card_eq_zero]
  left
  exact ⟨fun ⟨f, hf⟩ => boundary_ne_nil f hf⟩

/-- The Euler characteristic of the four-face presentation. -/
theorem eulerChar_presentation : eulerChar (presentation g) = 2 - 2 * g := by
  unfold eulerChar vertexCount
  rw [natCard_quot_presentation, emptyFaceCount_presentation, faces_length]
  have hE : (presentation g).edgeCount = 8 * g + 4 := card_edge
  rw [hE]
  push_cast
  ring

/-! ### Which edges lie on which face -/

/-- Whether an edge lies on the half sheet `(up, s)`. -/
def inFace (up s : Bool) : MEdge g → Bool
  | .seg s' _ => s' == s
  | .hole up' _ => up' == up
  | .outer up' _ => up' == up

theorem inFace_piece (up s : Bool) (k : Fin (2 * g + 1)) : inFace up s (piece up s k) = true := by
  unfold piece
  split_ifs <;> simp [inFace]

theorem inFace_faceDart (up s : Bool) (j : Fin (4 * g + 2)) :
    inFace up s (edgeOfDart (faceDart up s j)) = true := by
  obtain ⟨j, hj⟩ := j
  by_cases hle : j ≤ 2 * g
  · cases up
    · rw [faceDart_fl j (2 * g - j) hj (by omega) (by omega)]
      exact inFace_piece false s _
    · rw [faceDart_tu j (2 * g - j) hj (by omega) (by omega)]
      simp [inFace, edgeOfDart]
  · cases up
    · rw [faceDart_fu j (j - (2 * g + 1)) hj (by omega) (by omega)]
      simp [inFace, edgeOfDart]
    · rw [faceDart_tl j (j - (2 * g + 1)) hj (by omega) (by omega)]
      exact inFace_piece true s _

theorem exists_faceDart_of_inFace (up s : Bool) (e : MEdge g) (h : inFace up s e = true) :
    ∃ j, edgeOfDart (faceDart up s j) = e := by
  cases up with
  | false =>
    cases e with
    | seg s' j₀ =>
      have hs : s' = s := by simpa [inFace] using h
      subst hs
      have := j₀.isLt
      refine ⟨⟨2 * g - 2 * j₀.val, by omega⟩, ?_⟩
      rw [faceDart_fl (2 * g - 2 * j₀.val) (2 * j₀.val) (by omega) (by omega) (by omega)]
      exact (seg_eq_piece false _ j₀).symm
    | hole up' i =>
      have hu : up' = false := by simpa [inFace] using h
      subst hu
      have := i.isLt
      refine ⟨⟨2 * g - (2 * i.val + 1), by omega⟩, ?_⟩
      rw [faceDart_fl (2 * g - (2 * i.val + 1)) (2 * i.val + 1) (by omega) (by omega)
        (by omega)]
      exact (hole_eq_piece false s i).symm
    | outer up' k =>
      have hu : up' = false := by simpa [inFace] using h
      subst hu
      have := k.isLt
      refine ⟨⟨2 * g + 1 + k.val, by omega⟩, ?_⟩
      simp only [faceDart_fu (2 * g + 1 + k.val) k.val (by omega) k.isLt rfl, edgeOfDart, Fin.eta]
  | true =>
    cases e with
    | seg s' j₀ =>
      have hs : s' = s := by simpa [inFace] using h
      subst hs
      have := j₀.isLt
      refine ⟨⟨2 * g + 1 + 2 * j₀.val, by omega⟩, ?_⟩
      rw [faceDart_tl (2 * g + 1 + 2 * j₀.val) (2 * j₀.val) (by omega) (by omega) rfl]
      exact (seg_eq_piece true _ j₀).symm
    | hole up' i =>
      have hu : up' = true := by simpa [inFace] using h
      subst hu
      have := i.isLt
      refine ⟨⟨2 * g + 1 + (2 * i.val + 1), by omega⟩, ?_⟩
      rw [faceDart_tl (2 * g + 1 + (2 * i.val + 1)) (2 * i.val + 1) (by omega) (by omega) rfl]
      exact (hole_eq_piece true s i).symm
    | outer up' k =>
      have hu : up' = true := by simpa [inFace] using h
      subst hu
      have := k.isLt
      refine ⟨⟨2 * g - k.val, by omega⟩, ?_⟩
      simp only [faceDart_tu (2 * g - k.val) k.val (by omega) k.isLt (by omega), edgeOfDart, Fin.eta]

theorem mem_edges_faceWord (up s : Bool) (e : MEdge g) :
    e ∈ (faceWord up s).map edgeOfDart ↔ inFace up s e = true := by
  simp only [faceWord, List.map_ofFn, List.mem_ofFn, Function.comp_apply]
  exact ⟨fun ⟨j, hj⟩ => hj ▸ inFace_faceDart up s j, exists_faceDart_of_inFace up s e⟩

theorem faceEdge_injective (up s : Bool) :
    Function.Injective (fun j => edgeOfDart (faceDart (g := g) up s j)) := by
  rintro ⟨j, hj⟩ ⟨j', hj'⟩ h
  simp only at h
  apply Fin.ext
  show j = j'
  by_cases hle : j ≤ 2 * g <;> by_cases hle' : j' ≤ 2 * g
  · cases up
    · rw [faceDart_fl j (2 * g - j) hj (by omega) (by omega),
        faceDart_fl j' (2 * g - j') hj' (by omega) (by omega)] at h
      simp only [edgeOfDart] at h
      have := Fin.mk.inj_iff.mp (piece_injective false s h)
      omega
    · rw [faceDart_tu j (2 * g - j) hj (by omega) (by omega),
        faceDart_tu j' (2 * g - j') hj' (by omega) (by omega)] at h
      simp only [edgeOfDart, MEdge.outer.injEq, Fin.mk.injEq, eq_self_iff_true, true_and] at h
      omega
  · cases up
    · rw [faceDart_fl j (2 * g - j) hj (by omega) (by omega),
        faceDart_fu j' (j' - (2 * g + 1)) hj' (by omega) (by omega)] at h
      simp only [edgeOfDart] at h
      exact absurd h (piece_ne_outer _ _ _ _ _)
    · rw [faceDart_tu j (2 * g - j) hj (by omega) (by omega),
        faceDart_tl j' (j' - (2 * g + 1)) hj' (by omega) (by omega)] at h
      simp only [edgeOfDart] at h
      exact absurd h.symm (piece_ne_outer _ _ _ _ _)
  · cases up
    · rw [faceDart_fu j (j - (2 * g + 1)) hj (by omega) (by omega),
        faceDart_fl j' (2 * g - j') hj' (by omega) (by omega)] at h
      simp only [edgeOfDart] at h
      exact absurd h.symm (piece_ne_outer _ _ _ _ _)
    · rw [faceDart_tl j (j - (2 * g + 1)) hj (by omega) (by omega),
        faceDart_tu j' (2 * g - j') hj' (by omega) (by omega)] at h
      simp only [edgeOfDart] at h
      exact absurd h (piece_ne_outer _ _ _ _ _)
  · cases up
    · rw [faceDart_fu j (j - (2 * g + 1)) hj (by omega) (by omega),
        faceDart_fu j' (j' - (2 * g + 1)) hj' (by omega) (by omega)] at h
      simp only [edgeOfDart, MEdge.outer.injEq, Fin.mk.injEq, eq_self_iff_true, true_and] at h
      omega
    · rw [faceDart_tl j (j - (2 * g + 1)) hj (by omega) (by omega),
        faceDart_tl j' (j' - (2 * g + 1)) hj' (by omega) (by omega)] at h
      simp only [edgeOfDart] at h
      have := Fin.mk.inj_iff.mp (piece_injective true s h)
      omega

theorem nodup_edges_faceWord (up s : Bool) : ((faceWord (g := g) up s).map edgeOfDart).Nodup := by
  rw [faceWord, List.map_ofFn]
  exact List.nodup_ofFn.mpr (faceEdge_injective up s)

theorem count_edges_faceWord (up s : Bool) (e : MEdge g) :
    ((faceWord up s).map edgeOfDart).count e = if inFace up s e then 1 else 0 := by
  split_ifs with h
  · exact List.count_eq_one_of_mem (nodup_edges_faceWord up s) ((mem_edges_faceWord up s e).mpr h)
  · exact List.count_eq_zero_of_not_mem (fun hm => h ((mem_edges_faceWord up s e).mp hm))

theorem edgeOfDart_mapEquiv {α β : Type*} (e : α ≃ β) (d : SignedDart α) :
    edgeOfDart (SignedDart.mapEquiv e d) = e (edgeOfDart d) := by
  cases d <;> rfl

theorem edgeMultiplicity_presentation (e : (presentation g).Edge) :
    (presentation g).edgeMultiplicity e = 2 := by
  obtain ⟨e₀, rfl⟩ : ∃ e₀, εP g e₀ = e := ⟨_, Equiv.apply_symm_apply _ e⟩
  have key : ∀ up s, (((faceWord up s).map (SignedDart.mapEquiv (εP g))).map edgeOfDart).count
      (εP g e₀) = if inFace up s e₀ then 1 else 0 := by
    intro up s
    rw [List.map_map, show edgeOfDart ∘ SignedDart.mapEquiv (εP g) = εP g ∘ edgeOfDart from
        funext (edgeOfDart_mapEquiv _),
      ← List.map_map, List.count_map_of_injective _ _ (εP g).injective]
    exact count_edges_faceWord up s e₀
  unfold FiniteCyclicPresentation.edgeMultiplicity FiniteCyclicPresentation.faceEdgeMultiplicity
    FiniteCyclicPresentation.boundary
  simp only [List.get_eq_getElem]
  rw [Fin.sum_univ_fun_getElem (presentation g).faces
    (fun w => (w.map edgeOfDart).count (εP g e₀)), faces_eq]
  simp only [typedFaces, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, key]
  cases e₀ with
  | seg s j => cases s <;> simp [inFace]
  | hole up i => cases up <;> simp [inFace]
  | outer up k => cases up <;> simp [inFace]

theorem mem_edges_boundary (f : (presentation g).Face) (e₀ : MEdge g) :
    εP g e₀ ∈ ((presentation g).boundary f).map edgeOfDart ↔
      inFace (faceKey f).1 (faceKey f).2 e₀ = true := by
  rw [boundary_faceKey, List.map_map, ← mem_edges_faceWord]
  constructor
  · intro h
    obtain ⟨d, hd, hde⟩ := List.mem_map.mp h
    refine List.mem_map.mpr ⟨d, hd, ?_⟩
    apply (εP g).injective
    rw [← hde, Function.comp_apply, edgeOfDart_mapEquiv]
  · intro h
    obtain ⟨d, hd, hde⟩ := List.mem_map.mp h
    refine List.mem_map.mpr ⟨d, hd, ?_⟩
    rw [Function.comp_apply, edgeOfDart_mapEquiv, hde]

/-! ### Validity and connectivity -/

theorem isSurfaceValid_presentation : (presentation g).IsSurfaceValid := by
  refine ⟨⟨⟨0, by rw [faces_length]; omega⟩⟩, boundary_ne_nil, ?_,
    fun e => Or.inr (edgeMultiplicity_presentation e)⟩
  intro f f' hrot
  apply faceKey_injective
  have hmem : ∀ e₀ : MEdge g, inFace (faceKey f).1 (faceKey f).2 e₀ = true ↔
      inFace (faceKey f').1 (faceKey f').2 e₀ = true := by
    intro e₀
    rw [← mem_edges_boundary, ← mem_edges_boundary]
    exact (hrot.map edgeOfDart).mem_iff
  have h1 := (hmem (.seg (faceKey f).2 0)).mp (by simp only [inFace, beq_self_eq_true])
  have h2 := (hmem (.outer (faceKey f).1 0)).mp (by simp only [inFace, beq_self_eq_true])
  simp only [inFace, beq_iff_eq] at h1 h2
  exact Prod.ext h2 h1

/-- The faces of the presentation, by position. -/
def face (k : Fin 4) : (presentation g).Face := ⟨k.val, by rw [faces_length]; exact k.isLt⟩

theorem adjacent_of_common {f f' : (presentation g).Face} (e₀ : MEdge g)
    (h : inFace (faceKey f).1 (faceKey f).2 e₀ = true)
    (h' : inFace (faceKey f').1 (faceKey f').2 e₀ = true) :
    (presentation g).FaceAdjacent f f' :=
  ⟨_, (mem_edges_boundary f e₀).mpr h, (mem_edges_boundary f' e₀).mpr h'⟩

theorem isConnected_presentation : (presentation g).IsConnected := by
  refine ⟨⟨face 0⟩, ?_⟩
  have a01 : (presentation g).FaceAdjacent (face 0) (face 1) :=
    adjacent_of_common (.seg true 0) rfl rfl
  have a02 : (presentation g).FaceAdjacent (face 0) (face 2) :=
    adjacent_of_common (.outer true 0) rfl rfl
  have a23 : (presentation g).FaceAdjacent (face 2) (face 3) :=
    adjacent_of_common (.seg false 0) rfl rfl
  have symm : ∀ {f f' : (presentation g).Face}, (presentation g).FaceAdjacent f f' →
      (presentation g).FaceAdjacent f' f := fun ⟨e, he, he'⟩ => ⟨e, he', he⟩
  have hface : ∀ f : (presentation g).Face, ∃ k : Fin 4, f = face k := by
    rintro ⟨k, hk⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  have to0 : ∀ k : Fin 4, Relation.ReflTransGen (presentation g).FaceAdjacent (face k) (face 0) := by
    intro k
    fin_cases k
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (symm a01)
    · exact Relation.ReflTransGen.single (symm a02)
    · exact (Relation.ReflTransGen.single (symm a23)).tail (symm a02)
  have from0 : ∀ k : Fin 4, Relation.ReflTransGen (presentation g).FaceAdjacent (face 0) (face k) := by
    intro k
    fin_cases k
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single a01
    · exact Relation.ReflTransGen.single a02
    · exact (Relation.ReflTransGen.single a02).tail a23
  intro f f'
  obtain ⟨k, rfl⟩ := hface f
  obtain ⟨k', rfl⟩ := hface f'
  exact (to0 k).trans (from0 k')

end ModelPresentation
end R4Embedding
