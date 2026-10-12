import R4Initial.PresentationEuler

/-! Stage 07d(B), combinatorial half: the four-face presentation of the double of the planar
model `D_g` (the disk of radius `R = 3(g+1)` with `g` unit holes centred at `(3i, 0)`).

Each sheet of the double is cut along the `x`-axis into its upper and lower halves. A half is a
`(4g+2)`-gon. Write `x_0 = −R`, `x_{2i+1} = 3(i+1) − 1`, `x_{2i+2} = 3(i+1) + 1`, `x_{2g+1} = R`.

* The lower boundary of the upper half, in increasing `x`, has the `2g+1` pieces `[x_k, x_{k+1}]`:
  `x`-axis segments at even `k`, upper hole semicircles at odd `k`.
* The outer upper semicircle is cut above the same points into `2g+1` pieces.

The upper half is read counterclockwise from `(R, 0)`: first the outer pieces (in decreasing `x`),
then the lower pieces (in increasing `x`). The lower half is its mirror image, read as the inverse
word. Every edge is parametrized by increasing `x`.

There are `8g+4` edges, `6g+2` vertices and four faces, so `χ = 2 − 2g`. -/

namespace R4Embedding
namespace ModelPresentation

open R4CoS.Topology.ClassificationOfSurfaces SurfaceCellComplex FiniteCyclicPresentation

/-- Edges: `seg s j` is the `j`-th `x`-axis segment of sheet `s`, `hole up i` the upper or lower
semicircle of the `i`-th hole, `outer up k` the `k`-th piece of the upper or lower outer
semicircle. -/
inductive MEdge (g : ℕ)
  | seg (sheet : Bool) (j : Fin (g + 1))
  | hole (up : Bool) (i : Fin g)
  | outer (up : Bool) (k : Fin (2 * g + 1))
  deriving DecidableEq, Fintype

variable {g : ℕ}

/-! ### Pieces of the lower boundary of a half sheet -/

/-- The `k`-th piece of the lower boundary of a half sheet, in increasing `x`. -/
def piece (up s : Bool) (k : Fin (2 * g + 1)) : MEdge g :=
  if h : k.val % 2 = 0 then .seg s ⟨k.val / 2, by have := k.isLt; omega⟩
  else .hole up ⟨k.val / 2, by have := k.isLt; omega⟩

theorem piece_of_even {up s : Bool} {k : Fin (2 * g + 1)} (h : k.val % 2 = 0) :
    piece up s k = .seg s ⟨k.val / 2, by have := k.isLt; omega⟩ := by
  simp [piece, h]

theorem piece_of_odd {up s : Bool} {k : Fin (2 * g + 1)} (h : k.val % 2 = 1) :
    piece up s k = .hole up ⟨k.val / 2, by have := k.isLt; omega⟩ := by
  simp [piece, show k.val % 2 ≠ 0 by omega]

theorem piece_up_eq {up up' s : Bool} (k : ℕ) (hk : k < 2 * g + 1) (h : k % 2 = 0) :
    piece up s ⟨k, hk⟩ = piece up' s ⟨k, hk⟩ := by
  rw [piece_of_even h, piece_of_even h]

theorem piece_sheet_eq {up s s' : Bool} (k : ℕ) (hk : k < 2 * g + 1) (h : k % 2 = 1) :
    piece up s ⟨k, hk⟩ = piece up s' ⟨k, hk⟩ := by
  rw [piece_of_odd h, piece_of_odd h]

theorem seg_eq_piece (up s : Bool) (j : Fin (g + 1)) :
    MEdge.seg s j = piece up s ⟨2 * j.val, by have := j.isLt; omega⟩ := by
  rw [piece_of_even (show 2 * j.val % 2 = 0 by omega)]
  congr 1
  exact Fin.ext (show j.val = 2 * j.val / 2 by omega)

theorem hole_eq_piece (up s : Bool) (i : Fin g) :
    MEdge.hole up i = piece up s ⟨2 * i.val + 1, by have := i.isLt; omega⟩ := by
  rw [piece_of_odd (show (2 * i.val + 1) % 2 = 1 by omega)]
  congr 1
  exact Fin.ext (show i.val = (2 * i.val + 1) / 2 by omega)

theorem piece_ne_outer (up s up' : Bool) (k : Fin (2 * g + 1)) (k' : Fin (2 * g + 1)) :
    piece up s k ≠ .outer up' k' := by
  unfold piece
  split_ifs <;> simp

theorem piece_injective (up s : Bool) : Function.Injective (piece (g := g) up s) := by
  intro k k' h
  apply Fin.ext
  rcases Nat.mod_two_eq_zero_or_one k.val with hk | hk <;>
    rcases Nat.mod_two_eq_zero_or_one k'.val with hk' | hk'
  · rw [piece_of_even hk, piece_of_even hk'] at h
    simp only [MEdge.seg.injEq, Fin.mk.injEq] at h
    omega
  · rw [piece_of_even hk, piece_of_odd hk'] at h
    simp at h
  · rw [piece_of_odd hk, piece_of_even hk'] at h
    simp at h
  · rw [piece_of_odd hk, piece_of_odd hk'] at h
    simp only [MEdge.hole.injEq, Fin.mk.injEq] at h
    omega

/-! ### The face words -/

/-- The dart on side `j` of the half sheet `(up, s)`. -/
def faceDart (up s : Bool) (j : Fin (4 * g + 2)) : SignedDart (MEdge g) :=
  if up then
    if h : j.val ≤ 2 * g then .neg (.outer true ⟨2 * g - j.val, by omega⟩)
    else .pos (piece true s ⟨j.val - (2 * g + 1), by have := j.isLt; omega⟩)
  else
    if h : j.val ≤ 2 * g then .neg (piece false s ⟨2 * g - j.val, by omega⟩)
    else .pos (.outer false ⟨j.val - (2 * g + 1), by have := j.isLt; omega⟩)

theorem faceDart_tu {s : Bool} (j k : ℕ) (hj : j < 4 * g + 2) (hk : k < 2 * g + 1)
    (h : j + k = 2 * g) : faceDart true s ⟨j, hj⟩ = .neg (.outer true ⟨k, hk⟩) := by
  obtain rfl : k = 2 * g - j := by omega
  have hj' : j ≤ 2 * g := by omega
  simp [faceDart, hj']

theorem faceDart_tl {s : Bool} (j k : ℕ) (hj : j < 4 * g + 2) (hk : k < 2 * g + 1)
    (h : j = 2 * g + 1 + k) : faceDart true s ⟨j, hj⟩ = .pos (piece true s ⟨k, hk⟩) := by
  subst h
  have hn : ¬ (2 * g + 1 + k ≤ 2 * g) := by omega
  simp [faceDart, hn]

theorem faceDart_fl {s : Bool} (j k : ℕ) (hj : j < 4 * g + 2) (hk : k < 2 * g + 1)
    (h : j + k = 2 * g) : faceDart false s ⟨j, hj⟩ = .neg (piece false s ⟨k, hk⟩) := by
  obtain rfl : k = 2 * g - j := by omega
  have hj' : j ≤ 2 * g := by omega
  simp [faceDart, hj']

theorem faceDart_fu {s : Bool} (j k : ℕ) (hj : j < 4 * g + 2) (hk : k < 2 * g + 1)
    (h : j = 2 * g + 1 + k) : faceDart false s ⟨j, hj⟩ = .pos (.outer false ⟨k, hk⟩) := by
  subst h
  have hn : ¬ (2 * g + 1 + k ≤ 2 * g) := by omega
  simp [faceDart, hn]

/-- The boundary word of the half sheet `(up, s)`. -/
def faceWord (up s : Bool) : List (SignedDart (MEdge g)) := List.ofFn (faceDart up s)

theorem length_faceWord (up s : Bool) : (faceWord (g := g) up s).length = 4 * g + 2 := by
  simp [faceWord]

/-- The four half sheets. -/
def typedFaces (g : ℕ) : List (List (SignedDart (MEdge g))) :=
  [faceWord true true, faceWord false true, faceWord true false, faceWord false false]

theorem mem_typedFaces {w : List (SignedDart (MEdge g))} :
    w ∈ typedFaces g ↔ ∃ up s, w = faceWord up s := by
  simp only [typedFaces, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
  constructor
  · rintro (h | h | h | h) <;> exact ⟨_, _, h⟩
  · rintro ⟨up, s, rfl⟩
    cases up <;> cases s <;> simp

/-- The presentation, with the edges enumerated by `Fintype.equivFin`. -/
noncomputable def presentation (g : ℕ) : FiniteCyclicPresentation where
  edgeCount := Fintype.card (MEdge g)
  faces := (typedFaces g).map (List.map (SignedDart.mapEquiv (Fintype.equivFin (MEdge g))))

/-! ### Corners -/

local notation "Rg" => Corners.Rel (typedFaces g)

theorem rel_faceDart (up s : Bool) (j j' : Fin (4 * g + 2))
    (h : j'.val = (j.val + 1) % (4 * g + 2)) :
    Rg (Corners.finish (faceDart up s j)) (Corners.start (faceDart up s j')) := by
  refine ⟨faceWord up s, mem_typedFaces.mpr ⟨up, s, rfl⟩,
    (faceDart up s j, faceDart up s j'), ?_, rfl, rfl⟩
  rw [Corners.mem_pairs]
  refine ⟨j.val, by rw [length_faceWord]; exact j.isLt, ?_⟩
  simp only [faceWord, List.getElem_ofFn, List.length_ofFn]
  rw [Prod.mk.injEq]
  exact ⟨rfl, congrArg _ (Fin.ext h)⟩

theorem rel_succ (up s : Bool) (j : ℕ) (hj : j + 1 < 4 * g + 2) :
    Rg (Corners.finish (faceDart up s ⟨j, by omega⟩))
      (Corners.start (faceDart up s ⟨j + 1, hj⟩)) :=
  rel_faceDart up s _ _ (Nat.mod_eq_of_lt hj).symm

theorem rel_wrap (up s : Bool) :
    Rg (Corners.finish (faceDart up s ⟨4 * g + 1, by omega⟩))
      (Corners.start (faceDart up s ⟨0, by omega⟩)) :=
  rel_faceDart up s _ _ (by
    show 0 = (4 * g + 1 + 1) % (4 * g + 2)
    rw [show 4 * g + 1 + 1 = 4 * g + 2 by omega, Nat.mod_self])

theorem rel_outer_upper (m : ℕ) (hm : m < 2 * g) :
    Rg (.outer true ⟨m + 1, by omega⟩, false) (.outer true ⟨m, by omega⟩, true) := by
  have h := rel_succ (g := g) true true (2 * g - m - 1) (by omega)
  rwa [faceDart_tu (2 * g - m - 1) (m + 1) (by omega) (by omega) (by omega),
    faceDart_tu (2 * g - m - 1 + 1) m (by omega) (by omega) (by omega)] at h

theorem rel_outer_lower (m : ℕ) (hm : m < 2 * g) :
    Rg (.outer false ⟨m, by omega⟩, true) (.outer false ⟨m + 1, by omega⟩, false) := by
  have h := rel_succ (g := g) false true (2 * g + 1 + m) (by omega)
  rwa [faceDart_fu (2 * g + 1 + m) m (by omega) (by omega) rfl,
    faceDart_fu (2 * g + 1 + m + 1) (m + 1) (by omega) (by omega) (by omega)] at h

theorem rel_left_upper (s : Bool) :
    Rg (.outer true ⟨0, by omega⟩, false) (piece true s ⟨0, by omega⟩, false) := by
  have h := rel_succ (g := g) true s (2 * g) (by omega)
  rwa [faceDart_tu (2 * g) 0 (by omega) (by omega) (by omega),
    faceDart_tl (2 * g + 1) 0 (by omega) (by omega) (by omega)] at h

theorem rel_left_lower (s : Bool) :
    Rg (piece false s ⟨0, by omega⟩, false) (.outer false ⟨0, by omega⟩, false) := by
  have h := rel_succ (g := g) false s (2 * g) (by omega)
  rwa [faceDart_fl (2 * g) 0 (by omega) (by omega) (by omega),
    faceDart_fu (2 * g + 1) 0 (by omega) (by omega) (by omega)] at h

theorem rel_right_upper (s : Bool) :
    Rg (piece true s ⟨2 * g, by omega⟩, true) (.outer true ⟨2 * g, by omega⟩, true) := by
  have h := rel_wrap (g := g) true s
  rwa [faceDart_tl (4 * g + 1) (2 * g) (by omega) (by omega) (by omega),
    faceDart_tu 0 (2 * g) (by omega) (by omega) (by omega)] at h

theorem rel_right_lower (s : Bool) :
    Rg (.outer false ⟨2 * g, by omega⟩, true) (piece false s ⟨2 * g, by omega⟩, true) := by
  have h := rel_wrap (g := g) false s
  rwa [faceDart_fu (4 * g + 1) (2 * g) (by omega) (by omega) (by omega),
    faceDart_fl 0 (2 * g) (by omega) (by omega) (by omega)] at h

theorem rel_piece_upper (s : Bool) (k : ℕ) (hk : k < 2 * g) :
    Rg (piece true s ⟨k, by omega⟩, true) (piece true s ⟨k + 1, by omega⟩, false) := by
  have h := rel_succ (g := g) true s (2 * g + 1 + k) (by omega)
  rwa [faceDart_tl (2 * g + 1 + k) k (by omega) (by omega) rfl,
    faceDart_tl (2 * g + 1 + k + 1) (k + 1) (by omega) (by omega) (by omega)] at h

theorem rel_piece_lower (s : Bool) (k : ℕ) (hk : k < 2 * g) :
    Rg (piece false s ⟨k + 1, by omega⟩, false) (piece false s ⟨k, by omega⟩, true) := by
  have h := rel_succ (g := g) false s (2 * g - k - 1) (by omega)
  rwa [faceDart_fl (2 * g - k - 1) (k + 1) (by omega) (by omega) (by omega),
    faceDart_fl (2 * g - k - 1 + 1) k (by omega) (by omega) (by omega)] at h

/-! ### Vertices -/

/-- Vertices: `inl k` is the point `x_k` of the `x`-axis; `inr (up, m)` is the cut point of the
upper or lower outer semicircle above `x_{m+1}`. -/
abbrev MVertex (g : ℕ) := Fin (2 * g + 2) ⊕ (Bool × Fin (2 * g))

/-- The vertex at an end of an edge (`false` is the end with smaller `x`). -/
def vertexOf : MEdge g × Bool → MVertex g
  | (.seg _ j, false) => .inl ⟨2 * j.val, by have := j.isLt; omega⟩
  | (.seg _ j, true) => .inl ⟨2 * j.val + 1, by have := j.isLt; omega⟩
  | (.hole _ i, false) => .inl ⟨2 * i.val + 1, by have := i.isLt; omega⟩
  | (.hole _ i, true) => .inl ⟨2 * i.val + 2, by have := i.isLt; omega⟩
  | (.outer up k, false) =>
      if h : k.val = 0 then .inl ⟨0, by omega⟩
      else .inr (up, ⟨k.val - 1, by have := k.isLt; omega⟩)
  | (.outer up k, true) =>
      if h : k.val = 2 * g then .inl ⟨2 * g + 1, by omega⟩
      else .inr (up, ⟨k.val, by have := k.isLt; omega⟩)

theorem vertexOf_piece_false (up s : Bool) (k : ℕ) (hk : k < 2 * g + 1) :
    vertexOf (piece up s ⟨k, hk⟩, false) = .inl ⟨k, by omega⟩ := by
  rcases Nat.mod_two_eq_zero_or_one k with h2 | h2
  · rw [piece_of_even h2]
    simp only [vertexOf, Sum.inl.injEq, Fin.mk.injEq]
    omega
  · rw [piece_of_odd h2]
    simp only [vertexOf, Sum.inl.injEq, Fin.mk.injEq]
    omega

theorem vertexOf_piece_true (up s : Bool) (k : ℕ) (hk : k < 2 * g + 1) :
    vertexOf (piece up s ⟨k, hk⟩, true) = .inl ⟨k + 1, by omega⟩ := by
  rcases Nat.mod_two_eq_zero_or_one k with h2 | h2
  · rw [piece_of_even h2]
    simp only [vertexOf, Sum.inl.injEq, Fin.mk.injEq]
    omega
  · rw [piece_of_odd h2]
    simp only [vertexOf, Sum.inl.injEq, Fin.mk.injEq]
    omega

theorem vertexOf_outer_false_zero (up : Bool) (hk : 0 < 2 * g + 1) :
    vertexOf (.outer up ⟨0, hk⟩, false) = .inl ⟨0, by omega⟩ := by
  simp [vertexOf]

theorem vertexOf_outer_false_pos (up : Bool) (k : ℕ) (hk : k < 2 * g + 1) (h0 : k ≠ 0) :
    vertexOf (.outer up ⟨k, hk⟩, false) = .inr (up, ⟨k - 1, by omega⟩) := by
  simp [vertexOf, h0]

theorem vertexOf_outer_true_last (up : Bool) (hk : 2 * g < 2 * g + 1) :
    vertexOf (.outer up ⟨2 * g, hk⟩, true) = .inl ⟨2 * g + 1, by omega⟩ := by
  simp [vertexOf]

theorem vertexOf_outer_true_lt (up : Bool) (k : ℕ) (hk : k < 2 * g + 1) (h : k ≠ 2 * g) :
    vertexOf (.outer up ⟨k, hk⟩, true) = .inr (up, ⟨k, by omega⟩) := by
  simp [vertexOf, h]

/-- The two darts at a corner have ends at the same vertex. -/
theorem vertexOf_corner (up s : Bool) (j : ℕ) (hj : j < 4 * g + 2) :
    vertexOf (Corners.finish (faceDart up s ⟨j, hj⟩)) =
      vertexOf (Corners.start (faceDart up s ⟨(j + 1) % (4 * g + 2), Nat.mod_lt _ (by omega)⟩)) := by
  rcases (show j < 2 * g ∨ j = 2 * g ∨ (2 * g < j ∧ j < 4 * g + 1) ∨ j = 4 * g + 1 by omega)
    with h1 | h1 | h1 | h1
  · rw [show (⟨(j + 1) % (4 * g + 2), Nat.mod_lt _ (by omega)⟩ : Fin (4 * g + 2)) =
      ⟨j + 1, by omega⟩ from Fin.ext (Nat.mod_eq_of_lt (show j + 1 < 4 * g + 2 by omega))]
    cases up
    · rw [faceDart_fl j (2 * g - j) hj (by omega) (by omega),
        faceDart_fl (j + 1) (2 * g - j - 1) (by omega) (by omega) (by omega)]
      simp only [Corners.finish, Corners.start]
      rw [vertexOf_piece_false, vertexOf_piece_true]
      simp only [Sum.inl.injEq, Fin.mk.injEq]
      omega
    · rw [faceDart_tu j (2 * g - j) hj (by omega) (by omega),
        faceDart_tu (j + 1) (2 * g - j - 1) (by omega) (by omega) (by omega)]
      simp only [Corners.finish, Corners.start]
      rw [vertexOf_outer_false_pos true (2 * g - j) (by omega) (by omega),
        vertexOf_outer_true_lt true (2 * g - j - 1) (by omega) (by omega)]
  · subst h1
    rw [show (⟨(2 * g + 1) % (4 * g + 2), Nat.mod_lt _ (by omega)⟩ : Fin (4 * g + 2)) =
      ⟨2 * g + 1, by omega⟩ from Fin.ext (Nat.mod_eq_of_lt (show 2 * g + 1 < 4 * g + 2 by omega))]
    cases up
    · rw [faceDart_fl (2 * g) 0 hj (by omega) (by omega),
        faceDart_fu (2 * g + 1) 0 (by omega) (by omega) (by omega)]
      simp only [Corners.finish, Corners.start]
      rw [vertexOf_piece_false, vertexOf_outer_false_zero]
    · rw [faceDart_tu (2 * g) 0 hj (by omega) (by omega),
        faceDart_tl (2 * g + 1) 0 (by omega) (by omega) (by omega)]
      simp only [Corners.finish, Corners.start]
      rw [vertexOf_piece_false, vertexOf_outer_false_zero]
  · rw [show (⟨(j + 1) % (4 * g + 2), Nat.mod_lt _ (by omega)⟩ : Fin (4 * g + 2)) =
      ⟨j + 1, by omega⟩ from Fin.ext (Nat.mod_eq_of_lt (show j + 1 < 4 * g + 2 by omega))]
    cases up
    · rw [faceDart_fu j (j - (2 * g + 1)) hj (by omega) (by omega),
        faceDart_fu (j + 1) (j - 2 * g) (by omega) (by omega) (by omega)]
      simp only [Corners.finish, Corners.start]
      rw [vertexOf_outer_true_lt false (j - (2 * g + 1)) (by omega) (by omega),
        vertexOf_outer_false_pos false (j - 2 * g) (by omega) (by omega)]
      exact congrArg Sum.inr (Prod.ext rfl (Fin.ext (show j - (2 * g + 1) = j - 2 * g - 1 by omega)))
    · rw [faceDart_tl j (j - (2 * g + 1)) hj (by omega) (by omega),
        faceDart_tl (j + 1) (j - 2 * g) (by omega) (by omega) (by omega)]
      simp only [Corners.finish, Corners.start]
      rw [vertexOf_piece_true, vertexOf_piece_false]
      simp only [Sum.inl.injEq, Fin.mk.injEq]
      omega
  · subst h1
    rw [show (⟨(4 * g + 1 + 1) % (4 * g + 2), Nat.mod_lt _ (by omega)⟩ : Fin (4 * g + 2)) =
      ⟨0, by omega⟩ from Fin.ext (by
        show (4 * g + 1 + 1) % (4 * g + 2) = 0
        rw [show 4 * g + 1 + 1 = 4 * g + 2 by omega, Nat.mod_self])]
    cases up
    · rw [faceDart_fu (4 * g + 1) (2 * g) hj (by omega) (by omega),
        faceDart_fl 0 (2 * g) (by omega) (by omega) (by omega)]
      simp only [Corners.finish, Corners.start]
      rw [vertexOf_outer_true_last, vertexOf_piece_true]
    · rw [faceDart_tl (4 * g + 1) (2 * g) hj (by omega) (by omega),
        faceDart_tu 0 (2 * g) (by omega) (by omega) (by omega)]
      simp only [Corners.finish, Corners.start]
      rw [vertexOf_piece_true, vertexOf_outer_true_last]

theorem vertexOf_rel {x y : MEdge g × Bool} (h : Rg x y) : vertexOf x = vertexOf y := by
  obtain ⟨w, hw, q, hq, rfl, rfl⟩ := h
  obtain ⟨up, s, rfl⟩ := mem_typedFaces.mp hw
  rw [Corners.mem_pairs] at hq
  obtain ⟨i, hi, rfl⟩ := hq
  rw [length_faceWord] at hi
  simp only [faceWord, List.getElem_ofFn, List.length_ofFn]
  exact vertexOf_corner up s i hi

/-- A chosen end at each vertex. -/
def vertexRep : MVertex g → MEdge g × Bool
  | .inl ⟨0, _⟩ => (.outer true ⟨0, by omega⟩, false)
  | .inl ⟨k + 1, hk⟩ => (piece true true ⟨k, by omega⟩, true)
  | .inr (up, m) => (.outer up ⟨m.val, by have := m.isLt; omega⟩, true)

theorem vertexOf_vertexRep (v : MVertex g) : vertexOf (vertexRep v) = v := by
  rcases v with ⟨_ | k, hk⟩ | ⟨up, ⟨m, hm⟩⟩
  · exact vertexOf_outer_false_zero true (by omega)
  · exact vertexOf_piece_true true true k (by omega)
  · exact vertexOf_outer_true_lt up m (by omega) (by omega)

/-! ### Every end is joined to the chosen end of its vertex -/

theorem egSymm {α : Type*} {r : α → α → Prop} {x y : α} (h : Relation.EqvGen r x y) :
    Relation.EqvGen r y x :=
  Relation.EqvGen.symm _ _ h

theorem egTrans {α : Type*} {r : α → α → Prop} {x y z : α} (h₁ : Relation.EqvGen r x y)
    (h₂ : Relation.EqvGen r y z) : Relation.EqvGen r x z :=
  Relation.EqvGen.trans _ _ _ h₁ h₂

theorem eqvGen_axis (k : ℕ) (hk : k < 2 * g) (up s : Bool) :
    Relation.EqvGen Rg (piece up s ⟨k, by omega⟩, true) (piece true true ⟨k, by omega⟩, true) ∧
      Relation.EqvGen Rg (piece up s ⟨k + 1, by omega⟩, false)
        (piece true true ⟨k, by omega⟩, true) := by
  have A := fun s => Relation.EqvGen.rel _ _ (rel_piece_upper (g := g) s k hk)
  have B := fun s => Relation.EqvGen.rel _ _ (rel_piece_lower (g := g) s k hk)
  rcases Nat.mod_two_eq_zero_or_one k with hk2 | hk2
  · -- `k` is a segment, `k + 1` a hole
    have hA : ∀ up s, piece up s ⟨k, by omega⟩ = piece (g := g) true s ⟨k, by omega⟩ :=
      fun _ _ => piece_up_eq k (by omega) hk2
    have hB : ∀ up s, piece up s ⟨k + 1, by omega⟩ = piece (g := g) up true ⟨k + 1, by omega⟩ :=
      fun _ _ => piece_sheet_eq (k + 1) (by omega) (by omega)
    have key : ∀ s, Relation.EqvGen Rg (piece true s ⟨k, by omega⟩, true)
        (piece true true ⟨k, by omega⟩, true) := by
      intro s
      have h1 := A s
      rw [hB true s] at h1
      exact egTrans h1 (egSymm (A true))
    refine ⟨by rw [hA up s]; exact key s, ?_⟩
    rw [hB up s]
    cases up
    · have h2 := B true
      rw [hA false true] at h2
      exact h2
    · exact egSymm (A true)
  · -- `k` is a hole, `k + 1` a segment
    have hA : ∀ up s, piece up s ⟨k, by omega⟩ = piece (g := g) up true ⟨k, by omega⟩ :=
      fun _ _ => piece_sheet_eq k (by omega) hk2
    have hB : ∀ up s, piece up s ⟨k + 1, by omega⟩ = piece (g := g) true s ⟨k + 1, by omega⟩ :=
      fun _ _ => piece_up_eq (k + 1) (by omega) (by omega)
    have key : ∀ s, Relation.EqvGen Rg (piece true s ⟨k + 1, by omega⟩, false)
        (piece true true ⟨k, by omega⟩, true) := by
      intro s
      have h1 := A s
      rw [hA true s] at h1
      exact egSymm h1
    refine ⟨?_, by rw [hB up s]; exact key s⟩
    rw [hA up s]
    cases up
    · have h2 := B true
      rw [hB false true] at h2
      exact egTrans (egSymm h2) (key true)
    · exact Relation.EqvGen.refl _

theorem eqvGen_piece_rep (up s : Bool) (k : Fin (2 * g + 1)) (b : Bool) :
    Relation.EqvGen Rg (piece up s k, b) (vertexRep (vertexOf (piece up s k, b))) := by
  obtain ⟨k, hk⟩ := k
  cases b
  · rw [vertexOf_piece_false]
    cases k with
    | zero =>
      show Relation.EqvGen Rg (piece up s ⟨0, hk⟩, false) (MEdge.outer true ⟨0, by omega⟩, false)
      rw [piece_up_eq (up := up) (up' := true) (s := s) 0 hk (by omega)]
      exact egSymm (Relation.EqvGen.rel _ _ (rel_left_upper s))
    | succ m =>
      show Relation.EqvGen Rg (piece up s ⟨m + 1, hk⟩, false)
        (piece true true ⟨m, by omega⟩, true)
      exact (eqvGen_axis m (by omega) up s).2
  · rw [vertexOf_piece_true]
    show Relation.EqvGen Rg (piece up s ⟨k, hk⟩, true) (piece true true ⟨k, by omega⟩, true)
    by_cases hlast : k = 2 * g
    · subst hlast
      rw [piece_up_eq (up := up) (up' := true) (s := s) (2 * g) hk (by omega)]
      exact egTrans (Relation.EqvGen.rel _ _ (rel_right_upper s))
        (egSymm (Relation.EqvGen.rel _ _ (rel_right_upper true)))
    · exact (eqvGen_axis k (by omega) up s).1

theorem eqvGen_rep (x : MEdge g × Bool) : Relation.EqvGen Rg x (vertexRep (vertexOf x)) := by
  obtain ⟨e, b⟩ := x
  cases e with
  | seg s j =>
    rw [seg_eq_piece true s j]
    exact eqvGen_piece_rep true s _ b
  | hole up i =>
    rw [hole_eq_piece up true i]
    exact eqvGen_piece_rep up true _ b
  | outer up k =>
    obtain ⟨k, hk⟩ := k
    cases b
    · cases k with
      | zero =>
        rw [vertexOf_outer_false_zero]
        show Relation.EqvGen Rg (MEdge.outer up ⟨0, hk⟩, false)
          (MEdge.outer true ⟨0, by omega⟩, false)
        cases up
        · have h1 := Relation.EqvGen.rel _ _ (rel_left_lower (g := g) true)
          have h2 := Relation.EqvGen.rel _ _ (rel_left_upper (g := g) true)
          rw [piece_up_eq (up := false) (up' := true) (s := true) 0 (by omega) (by omega)] at h1
          exact egTrans (egSymm h1) (egSymm h2)
        · exact Relation.EqvGen.refl _
      | succ m =>
        rw [vertexOf_outer_false_pos up (m + 1) hk (by omega)]
        show Relation.EqvGen Rg (MEdge.outer up ⟨m + 1, hk⟩, false)
          (MEdge.outer up ⟨m, by omega⟩, true)
        cases up
        · exact egSymm (Relation.EqvGen.rel _ _ (rel_outer_lower (g := g) m (by omega)))
        · exact Relation.EqvGen.rel _ _ (rel_outer_upper (g := g) m (by omega))
    · by_cases hlast : k = 2 * g
      · subst hlast
        rw [vertexOf_outer_true_last]
        show Relation.EqvGen Rg (MEdge.outer up ⟨2 * g, hk⟩, true)
          (piece true true ⟨2 * g, by omega⟩, true)
        cases up
        · have h1 := Relation.EqvGen.rel _ _ (rel_right_lower (g := g) true)
          rw [piece_up_eq (up := false) (up' := true) (s := true) (2 * g) (by omega) (by omega)] at h1
          exact h1
        · exact egSymm (Relation.EqvGen.rel _ _ (rel_right_upper (g := g) true))
      · rw [vertexOf_outer_true_lt up k hk hlast]
        exact Relation.EqvGen.refl _

/-- Counting classes through a labelling with chosen representatives. -/
theorem natCard_quot_eq_of_label {α β : Type*} {r : α → α → Prop} (ℓ : α → β) (rep : β → α)
    (hrel : ∀ x y, r x y → ℓ x = ℓ y) (hrep : ∀ x, Relation.EqvGen r x (rep (ℓ x)))
    (hℓ : ∀ v, ℓ (rep v) = v) :
    Nat.card (Quot r) = Nat.card β := by
  refine Nat.card_congr
    { toFun := Quot.lift ℓ hrel
      invFun := fun v => Quot.mk _ (rep v)
      left_inv := fun q => ?_
      right_inv := fun v => hℓ v }
  induction q using Quot.ind with
  | mk x => exact (Quot.eqvGen_sound (hrep x)).symm

theorem natCard_quot_typedFaces : Nat.card (Quot (Corners.Rel (typedFaces g))) = 6 * g + 2 := by
  rw [natCard_quot_eq_of_label vertexOf vertexRep (fun _ _ h => vertexOf_rel h) eqvGen_rep
    vertexOf_vertexRep, Nat.card_eq_fintype_card]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  ring

/-- Relabelling the edges of every face by an equivalence does not change the corner classes. -/
theorem natCard_quot_map_mapEquiv {α β : Type*} (e : α ≃ β) (L : List (List (SignedDart α))) :
    Nat.card (Quot (Corners.Rel (L.map (List.map (SignedDart.mapEquiv e))))) =
      Nat.card (Quot (Corners.Rel L)) := by
  symm
  refine natCard_quot_eq_of_maps (Prod.map e id) (Prod.map e.symm id) ?_ ?_ ?_ ?_
  · rintro x y ⟨w, hw, q, hq, rfl, rfl⟩
    apply Relation.EqvGen.rel
    refine ⟨w.map (SignedDart.mapEquiv e), List.mem_map_of_mem hw,
      Prod.map (SignedDart.mapEquiv e) (SignedDart.mapEquiv e) q, ?_, ?_, ?_⟩
    · rw [Corners.pairs_map]
      exact List.mem_map_of_mem hq
    · simp [finish_mapEquiv]
    · simp [start_mapEquiv]
  · rintro u v ⟨w, hw, q, hq, rfl, rfl⟩
    rw [List.mem_map] at hw
    obtain ⟨w₀, hw₀, rfl⟩ := hw
    rw [Corners.pairs_map, List.mem_map] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    apply Relation.EqvGen.rel
    refine ⟨w₀, hw₀, q', hq', ?_, ?_⟩
    · simp only [Prod.map_fst, finish_mapEquiv]
      obtain ⟨a, b⟩ := Corners.finish q'.1
      simp
    · simp only [Prod.map_snd, start_mapEquiv]
      obtain ⟨a, b⟩ := Corners.start q'.2
      simp
  · rintro ⟨a, b⟩
    simp only [Prod.map, Equiv.symm_apply_apply, id]
    exact Relation.EqvGen.refl _
  · rintro ⟨a, b⟩
    simp only [Prod.map, Equiv.apply_symm_apply, id]
    exact Relation.EqvGen.refl _

theorem natCard_quot_presentation :
    Nat.card (Quot (Corners.Rel (presentation g).faces)) = 6 * g + 2 :=
  (natCard_quot_map_mapEquiv _ _).trans natCard_quot_typedFaces

end ModelPresentation
end R4Embedding
