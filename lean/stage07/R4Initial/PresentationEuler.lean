import R4CoS.FiniteCyclicNormalization
import R4CoS.FiniteCyclicUnorientedRealization
import R4CoS.FiniteCyclicCanonical

/-! Euler characteristic of finite cyclic presentations.

A presentation is a list of cyclic boundary words in signed edges. Its vertices are the ends
of edges (tail or head), glued at each corner: the end where a dart finishes is the end where
the next dart of the same face starts. A face with an empty word is a sphere by itself and
contributes one vertex of its own. The Euler characteristic is `V − E + F`.

This file sets up the corner relation and proves that it is unchanged under the operations on
words that Lean Pool's normalization moves use (rotation, relabeling, reversal), together with
a general criterion for two relations to have the same number of classes. -/

noncomputable section
namespace R4Embedding

open R4CoS.Topology.ClassificationOfSurfaces
open SurfaceCellComplex FiniteCyclicPresentation

namespace Corners

variable {α β : Type*}

theorem nil_or_ne_nil (l : List α) : l = [] ∨ l ≠ [] := em _

/-- The end of an edge at which a dart starts: the tail (`false`) of a positive dart, the
head (`true`) of a negative one. -/
def start : SignedDart α → α × Bool
  | .pos e => (e, false)
  | .neg e => (e, true)

/-- The end of an edge at which a dart finishes. -/
def finish : SignedDart α → α × Bool
  | .pos e => (e, true)
  | .neg e => (e, false)

@[simp] theorem start_flip (d : SignedDart α) : start d.flip = finish d := by
  cases d <;> rfl

@[simp] theorem finish_flip (d : SignedDart α) : finish d.flip = start d := by
  cases d <;> rfl

/-- Consecutive pairs of a cyclic word, including the wrap-around pair. -/
def pairs : List α → List (α × α)
  | [] => []
  | d :: ds => List.zip (d :: ds) (ds ++ [d])

theorem pairs_eq_zip_rotate (l : List α) : pairs l = List.zip l (l.rotate 1) := by
  cases l with
  | nil => rfl
  | cons d ds => simp [pairs, List.rotate_cons_succ]

theorem length_pairs (l : List α) : (pairs l).length = l.length := by
  rw [pairs_eq_zip_rotate, List.length_zip, List.length_rotate, min_self]

theorem mem_pairs {l : List α} {q : α × α} :
    q ∈ pairs l ↔ ∃ (i : ℕ) (hi : i < l.length),
      q = (l[i], l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega))) := by
  rw [pairs_eq_zip_rotate, List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hil : i < l.length := by simpa using hi
    refine ⟨i, hil, ?_⟩
    rw [List.getElem_zip, List.getElem_rotate]
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, by simpa using hi, ?_⟩
    rw [List.getElem_zip, List.getElem_rotate]

theorem zip_rotate {l₁ : List α} {l₂ : List β} (h : l₁.length = l₂.length) (k : ℕ) :
    List.zip (l₁.rotate k) (l₂.rotate k) = (List.zip l₁ l₂).rotate k := by
  apply List.ext_getElem
  · simp [h]
  · intro i hi₁ hi₂
    have hl : (List.zip l₁ l₂).length = l₁.length := by simp [h]
    simp only [List.getElem_zip, List.getElem_rotate, hl, h]

theorem pairs_rotate (l : List α) (k : ℕ) : pairs (l.rotate k) = (pairs l).rotate k := by
  rw [pairs_eq_zip_rotate, pairs_eq_zip_rotate, List.rotate_rotate, Nat.add_comm,
    ← List.rotate_rotate, zip_rotate (by simp)]

theorem mem_pairs_rotate {l : List α} (k : ℕ) {q : α × α} :
    q ∈ pairs (l.rotate k) ↔ q ∈ pairs l := by
  rw [pairs_rotate, List.mem_rotate]

theorem mem_pairs_of_isRotated {l l' : List α} (h : l ~r l') {q : α × α} :
    q ∈ pairs l' ↔ q ∈ pairs l := by
  obtain ⟨k, rfl⟩ := h
  exact mem_pairs_rotate k

theorem pairs_map (f : α → β) (l : List α) :
    pairs (l.map f) = (pairs l).map (Prod.map f f) := by
  rw [pairs_eq_zip_rotate, pairs_eq_zip_rotate, ← List.map_rotate, List.zip_map]

theorem mem_pairs_reverse {l : List α} {q : α × α} :
    q ∈ pairs l.reverse ↔ q.swap ∈ pairs l := by
  by_cases hne : l = []
  · subst hne
    simp [pairs]
  have hn : 0 < l.length := List.length_pos_iff.mpr hne
  have key : ∀ {a b : ℕ} (ha : a < l.length) (hb : b < l.length), a = b → l[a] = l[b] := by
    rintro a b ha hb rfl
    rfl
  rw [mem_pairs, mem_pairs]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [List.length_reverse] at hi
    refine ⟨l.length - 1 - (i + 1) % l.length, by omega, ?_⟩
    simp only [Prod.swap_prod_mk, List.getElem_reverse, List.length_reverse]
    refine Prod.ext (key _ _ rfl) (key _ _ ?_)
    rcases Nat.lt_or_ge (i + 1) l.length with h | h
    · rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]
      omega
    · have h' : i + 1 = l.length := by omega
      rw [h', Nat.mod_self, Nat.sub_zero, Nat.sub_add_cancel hn, Nat.mod_self]
      omega
  · rintro ⟨j, hj, hq⟩
    obtain ⟨a, b⟩ := q
    simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    refine ⟨l.length - 1 - (j + 1) % l.length, by rw [List.length_reverse]; omega, ?_⟩
    simp only [List.getElem_reverse, List.length_reverse]
    refine Prod.ext (key _ _ ?_) (key _ _ ?_)
    · rcases Nat.lt_or_ge (j + 1) l.length with h | h
      · rw [Nat.mod_eq_of_lt h]
        omega
      · have h' : j + 1 = l.length := by omega
        rw [h', Nat.mod_self]
        omega
    · rcases Nat.lt_or_ge (j + 1) l.length with h | h
      · rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]
        omega
      · have h' : j + 1 = l.length := by omega
        rw [h', Nat.mod_self, Nat.sub_zero, Nat.sub_add_cancel hn, Nat.mod_self]
        omega

theorem mem_pairs_inverseWord {w : List (SignedDart α)} {q : SignedDart α × SignedDart α} :
    q ∈ pairs (inverseWord w) ↔ ∃ p ∈ pairs w, q = (p.2.flip, p.1.flip) := by
  rw [inverseWord, pairs_map, List.mem_map]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r.swap, mem_pairs_reverse.mp hr, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.swap, mem_pairs_reverse.mpr (by simpa using hp), rfl⟩

/-- Ends of edges under an edge relabeling: a reversed edge swaps its tail and head. -/
def endMap (e : EdgeRelabeling α β) (x : α × Bool) : β × Bool :=
  (e.edgeEquiv x.1, xor x.2 (e.reverse x.1))

theorem start_mapDart (e : EdgeRelabeling α β) (d : SignedDart α) :
    start (e.mapDart d) = endMap e (start d) := by
  cases d with
  | pos a => cases h : e.reverse a <;> simp [EdgeRelabeling.mapDart, endMap, start, h]
  | neg a => cases h : e.reverse a <;> simp [EdgeRelabeling.mapDart, endMap, start, h]

theorem finish_mapDart (e : EdgeRelabeling α β) (d : SignedDart α) :
    finish (e.mapDart d) = endMap e (finish d) := by
  cases d with
  | pos a => cases h : e.reverse a <;> simp [EdgeRelabeling.mapDart, endMap, finish, h]
  | neg a => cases h : e.reverse a <;> simp [EdgeRelabeling.mapDart, endMap, finish, h]

/-- `endMap` as an equivalence. -/
def endEquiv (e : EdgeRelabeling α β) : α × Bool ≃ β × Bool where
  toFun := endMap e
  invFun y := (e.edgeEquiv.symm y.1, xor y.2 (e.reverse (e.edgeEquiv.symm y.1)))
  left_inv x := by
    obtain ⟨a, b⟩ := x
    cases b <;> cases h : e.reverse a <;> simp [endMap, h]
  right_inv y := by
    obtain ⟨c, b⟩ := y
    cases b <;> cases h : e.reverse (e.edgeEquiv.symm c) <;> simp [endMap, h]

theorem endEquiv_apply (e : EdgeRelabeling α β) (x : α × Bool) : endEquiv e x = endMap e x := rfl

/-- Consecutive pairs of a linear list. -/
def lin (l : List α) : List (α × α) := List.zip l l.tail

@[simp] theorem lin_nil : lin ([] : List α) = [] := rfl

@[simp] theorem lin_singleton (a : α) : lin [a] = [] := rfl

@[simp] theorem lin_cons_cons (a b : α) (l : List α) :
    lin (a :: b :: l) = (a, b) :: lin (b :: l) := rfl

theorem lin_cons_of_ne_nil (a : α) {l : List α} (hl : l ≠ []) :
    lin (a :: l) = (a, l.head hl) :: lin l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons b l => rfl

theorem mem_lin_append {l₁ l₂ : List α} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) {q : α × α} :
    q ∈ lin (l₁ ++ l₂) ↔ q ∈ lin l₁ ∨ q = (l₁.getLast h₁, l₂.head h₂) ∨ q ∈ lin l₂ := by
  induction l₁ with
  | nil => exact absurd rfl h₁
  | cons a t ih =>
    by_cases ht : t = []
    · subst ht
      simp [lin_cons_of_ne_nil a h₂]
    · rw [List.cons_append, lin_cons_of_ne_nil a (List.append_ne_nil_of_left_ne_nil ht l₂),
        lin_cons_of_ne_nil a ht, List.mem_cons, List.mem_cons, ih ht, List.getLast_cons ht,
        List.head_append_of_ne_nil ht]
      tauto

theorem zip_append_singleton_left {l : List α} {l' : List β} (x : α)
    (h : l'.length ≤ l.length) : List.zip (l ++ [x]) l' = List.zip l l' := by
  induction l generalizing l' with
  | nil =>
    have : l' = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst this
    simp
  | cons a t ih =>
    cases l' with
    | nil => simp
    | cons b l' =>
      simp only [List.cons_append, List.zip_cons_cons]
      rw [ih (by simpa using h)]

theorem pairs_cons_eq_lin (d : α) (ds : List α) : pairs (d :: ds) = lin (d :: ds ++ [d]) := by
  simp only [pairs, lin, List.cons_append, List.tail_cons]
  rw [← List.cons_append, zip_append_singleton_left _ (by simp)]

/-- Consecutive pairs of a flattened list, followed by the first element of one more block. -/
theorem mem_lin_flatMap_append {B : α → List β} (hB : ∀ a, B a ≠ []) (x : α) :
    ∀ (u : List α) (q : β × β),
      q ∈ lin (u.flatMap B ++ [(B x).head (hB x)]) ↔
        (∃ a ∈ u, q ∈ lin (B a)) ∨
          ∃ p ∈ lin (u ++ [x]), q = ((B p.1).getLast (hB _), (B p.2).head (hB _)) := by
  intro u
  induction u with
  | nil => intro q; simp
  | cons a u ih =>
    intro q
    have hrest : u.flatMap B ++ [(B x).head (hB x)] ≠ [] := by simp
    have hux : u ++ [x] ≠ [] := by simp
    have hhead : (u.flatMap B ++ [(B x).head (hB x)]).head hrest =
        (B ((u ++ [x]).head hux)).head (hB _) := by
      cases u with
      | nil => simp
      | cons b u => simp [List.head_append_of_ne_nil (hB b)]
    rw [List.flatMap_cons, List.append_assoc, mem_lin_append (hB a) hrest, ih,
      List.cons_append, lin_cons_of_ne_nil a hux, hhead]
    constructor
    · rintro (h | h | ⟨b, hb, h⟩ | ⟨p, hp, h⟩)
      · exact Or.inl ⟨a, List.mem_cons.mpr (Or.inl rfl), h⟩
      · exact Or.inr ⟨_, List.mem_cons.mpr (Or.inl rfl), h⟩
      · exact Or.inl ⟨b, List.mem_cons.mpr (Or.inr hb), h⟩
      · exact Or.inr ⟨p, List.mem_cons.mpr (Or.inr hp), h⟩
    · rintro (⟨b, hb, h⟩ | ⟨p, hp, h⟩)
      · rcases List.mem_cons.mp hb with rfl | hb
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl ⟨b, hb, h⟩))
      · rcases List.mem_cons.mp hp with rfl | hp
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr ⟨p, hp, h⟩))

/-- Corners of a word in which each letter is replaced by a nonempty block: the corners inside
blocks, and the corners between consecutive blocks. -/
theorem mem_pairs_flatMap {B : α → List β} (hB : ∀ a, B a ≠ []) {w : List α} {q : β × β} :
    q ∈ pairs (w.flatMap B) ↔ (∃ a ∈ w, q ∈ lin (B a)) ∨
      ∃ p ∈ pairs w, q = ((B p.1).getLast (hB _), (B p.2).head (hB _)) := by
  cases w with
  | nil => simp [pairs]
  | cons d ds =>
    have hW : (d :: ds).flatMap B = (B d).head (hB d) :: ((B d).tail ++ ds.flatMap B) := by
      obtain ⟨b, bs, hbs⟩ := List.exists_cons_of_ne_nil (hB d)
      simp [List.flatMap_cons, hbs]
    rw [hW, pairs_cons_eq_lin, ← hW, pairs_cons_eq_lin d ds,
      mem_lin_flatMap_append hB d (d :: ds) q]

theorem mem_pairs_append {A B : List α} (hA : A ≠ []) (hB : B ≠ []) {q : α × α} :
    q ∈ pairs (A ++ B) ↔ q ∈ lin A ∨ q = (A.getLast hA, B.head hB) ∨ q ∈ lin B ∨
      q = (B.getLast hB, A.head hA) := by
  obtain ⟨a, A', rfl⟩ := List.exists_cons_of_ne_nil hA
  have hBa : B ++ [a] ≠ [] := by simp
  rw [List.cons_append, pairs_cons_eq_lin, ← List.cons_append, List.append_assoc,
    mem_lin_append hA hBa, mem_lin_append hB (List.cons_ne_nil a []),
    List.head_append_of_ne_nil hB]
  simp

theorem mem_pairs_singleton (d : α) {q : α × α} : q ∈ pairs [d] ↔ q = (d, d) := by
  simp [pairs]

theorem lin_map (f : α → β) (l : List α) : lin (l.map f) = (lin l).map (Prod.map f f) := by
  cases l with
  | nil => rfl
  | cons a l =>
    show List.zip (f a :: l.map f) (l.map f) = (List.zip (a :: l) l).map (Prod.map f f)
    rw [show f a :: l.map f = (a :: l).map f from rfl, List.zip_map]

/-- The corner relation of a list of cyclic words: the end where a dart finishes is glued to
the end where the next dart starts. -/
def Rel (L : List (List (SignedDart α))) (x y : α × Bool) : Prop :=
  ∃ w ∈ L, ∃ q ∈ pairs w, x = finish q.1 ∧ y = start q.2

/-- Corner gluings of one cyclic word. -/
def Of (w : List (SignedDart α)) (x y : α × Bool) : Prop :=
  ∃ q ∈ pairs w, x = finish q.1 ∧ y = start q.2

/-- Corner gluings between consecutive letters of a linear word. -/
def OfLin (w : List (SignedDart α)) (x y : α × Bool) : Prop :=
  ∃ q ∈ lin w, x = finish q.1 ∧ y = start q.2

theorem of_isRotated {w w' : List (SignedDart α)} (h : w ~r w') {x y : α × Bool} :
    Of w' x y ↔ Of w x y := by
  simp only [Of, mem_pairs_of_isRotated h]

theorem of_inverseWord {w : List (SignedDart α)} {x y : α × Bool} :
    Of (inverseWord w) x y ↔ Of w y x := by
  constructor
  · rintro ⟨q, hq, hx, hy⟩
    obtain ⟨p, hp, rfl⟩ := mem_pairs_inverseWord.mp hq
    exact ⟨p, hp, by simpa using hy, by simpa using hx⟩
  · rintro ⟨p, hp, hy, hx⟩
    exact ⟨(p.2.flip, p.1.flip), mem_pairs_inverseWord.mpr ⟨p, hp, rfl⟩,
      by simpa using hx, by simpa using hy⟩

theorem of_append {A B : List (SignedDart α)} (hA : A ≠ []) (hB : B ≠ []) {x y : α × Bool} :
    Of (A ++ B) x y ↔ OfLin A x y ∨ (x = finish (A.getLast hA) ∧ y = start (B.head hB)) ∨
      OfLin B x y ∨ (x = finish (B.getLast hB) ∧ y = start (A.head hA)) := by
  simp only [Of, OfLin, mem_pairs_append hA hB]
  constructor
  · rintro ⟨q, hq | rfl | hq | rfl, hx, hy⟩
    · exact Or.inl ⟨q, hq, hx, hy⟩
    · exact Or.inr (Or.inl ⟨hx, hy⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨q, hq, hx, hy⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hx, hy⟩))
  · rintro (⟨q, hq, hx, hy⟩ | ⟨hx, hy⟩ | ⟨q, hq, hx, hy⟩ | ⟨hx, hy⟩)
    · exact ⟨q, Or.inl hq, hx, hy⟩
    · exact ⟨_, Or.inr (Or.inl rfl), hx, hy⟩
    · exact ⟨q, Or.inr (Or.inr (Or.inl hq)), hx, hy⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), hx, hy⟩

theorem of_singleton (d : SignedDart α) {x y : α × Bool} :
    Of [d] x y ↔ x = finish d ∧ y = start d := by
  simp [Of, mem_pairs_singleton]

theorem ofLin_singleton (d : SignedDart α) {x y : α × Bool} : ¬ OfLin [d] x y := by
  simp [OfLin]

/-- A nonempty cyclic word: its linear corners and the wrap-around corner. -/
theorem of_iff_ofLin_or_wrap {w : List (SignedDart α)} (hw : w ≠ []) {x y : α × Bool} :
    Of w x y ↔ OfLin w x y ∨ (x = finish (w.getLast hw) ∧ y = start (w.head hw)) := by
  obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hw
  simp only [Of, OfLin, pairs_cons_eq_lin, mem_lin_append hw (List.cons_ne_nil d []),
    lin_singleton, List.not_mem_nil, or_false, List.head_cons]
  constructor
  · rintro ⟨q, hq | rfl, hx, hy⟩
    · exact Or.inl ⟨q, hq, hx, hy⟩
    · exact Or.inr ⟨hx, hy⟩
  · rintro (⟨q, hq, hx, hy⟩ | ⟨hx, hy⟩)
    · exact ⟨q, Or.inl hq, hx, hy⟩
    · exact ⟨_, Or.inr rfl, hx, hy⟩

theorem ofLin_of_ofLin_append_left {A B : List (SignedDart α)} {x y : α × Bool}
    (h : OfLin A x y) : OfLin (A ++ B) x y := by
  obtain ⟨q, hq, hx, hy⟩ := h
  refine ⟨q, ?_, hx, hy⟩
  rcases nil_or_ne_nil A with rfl | hA
  · simp at hq
  rcases nil_or_ne_nil B with rfl | hB
  · simpa using hq
  exact (mem_lin_append hA hB).mpr (Or.inl hq)

theorem ofLin_of_ofLin_append_right {A B : List (SignedDart α)} {x y : α × Bool}
    (h : OfLin B x y) : OfLin (A ++ B) x y := by
  obtain ⟨q, hq, hx, hy⟩ := h
  refine ⟨q, ?_, hx, hy⟩
  rcases nil_or_ne_nil B with rfl | hB
  · simp at hq
  rcases nil_or_ne_nil A with rfl | hA
  · simpa using hq
  exact (mem_lin_append hA hB).mpr (Or.inr (Or.inr hq))

theorem of_of_ofLin {w : List (SignedDart α)} {x y : α × Bool} (h : OfLin w x y) :
    Of w x y := by
  rcases nil_or_ne_nil w with rfl | hw
  · obtain ⟨q, hq, -⟩ := h
    simp at hq
  exact (of_iff_ofLin_or_wrap hw).mpr (Or.inl h)

/-- Corner gluings of a cyclic word read in either direction. -/
def SOf (w : List (SignedDart α)) (x y : α × Bool) : Prop := Of w x y ∨ Of w y x

theorem sOf_comm {w : List (SignedDart α)} {x y : α × Bool} : SOf w x y ↔ SOf w y x :=
  Or.comm

theorem sOf_isRotated {w w' : List (SignedDart α)} (h : w ~r w') {x y : α × Bool} :
    SOf w' x y ↔ SOf w x y := by
  simp only [SOf, of_isRotated h]

theorem sOf_inverseWord {w : List (SignedDart α)} {x y : α × Bool} :
    SOf (inverseWord w) x y ↔ SOf w x y := by
  simp only [SOf, of_inverseWord, Or.comm]

end Corners

/-! ### Counting classes -/

theorem eqvGen_map {α β : Type*} {r : α → α → Prop} {s : β → β → Prop} (φ : α → β)
    (hφ : ∀ x y, r x y → Relation.EqvGen s (φ x) (φ y)) {x y : α}
    (h : Relation.EqvGen r x y) : Relation.EqvGen s (φ x) (φ y) := by
  induction h with
  | rel x y hxy => exact hφ x y hxy
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Two relations have equivalent quotients when maps in both directions respect them and are
inverse up to the relations. -/
def quotEquivOfMaps {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}
    (φ : α → β) (ψ : β → α)
    (hφ : ∀ x y, r x y → Relation.EqvGen s (φ x) (φ y))
    (hψ : ∀ u v, s u v → Relation.EqvGen r (ψ u) (ψ v))
    (hψφ : ∀ x, Relation.EqvGen r (ψ (φ x)) x)
    (hφψ : ∀ u, Relation.EqvGen s (φ (ψ u)) u) : Quot r ≃ Quot s where
  toFun := Quot.lift (fun x => Quot.mk s (φ x)) fun x y h => Quot.eqvGen_sound (hφ x y h)
  invFun := Quot.lift (fun u => Quot.mk r (ψ u)) fun u v h => Quot.eqvGen_sound (hψ u v h)
  left_inv := by
    intro q
    induction q using Quot.ind with
    | mk x => exact Quot.eqvGen_sound (hψφ x)
  right_inv := by
    intro q
    induction q using Quot.ind with
    | mk u => exact Quot.eqvGen_sound (hφψ u)

theorem natCard_quot_eq_of_maps {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}
    (φ : α → β) (ψ : β → α)
    (hφ : ∀ x y, r x y → Relation.EqvGen s (φ x) (φ y))
    (hψ : ∀ u v, s u v → Relation.EqvGen r (ψ u) (ψ v))
    (hψφ : ∀ x, Relation.EqvGen r (ψ (φ x)) x)
    (hφψ : ∀ u, Relation.EqvGen s (φ (ψ u)) u) :
    Nat.card (Quot r) = Nat.card (Quot s) :=
  Nat.card_congr (quotEquivOfMaps φ ψ hφ hψ hψφ hφψ)

/-! ### Vertices and the Euler characteristic of a presentation -/

/-- Faces whose boundary word is empty (each is a sphere with one vertex). -/
def emptyFaceCount (P : FiniteCyclicPresentation) : ℕ :=
  Nat.card {f : P.Face // P.boundary f = []}

/-- Number of vertices: classes of edge ends under the corner gluing, plus one for each face
with an empty word. -/
def vertexCount (P : FiniteCyclicPresentation) : ℕ :=
  Nat.card (Quot (Corners.Rel P.faces)) + emptyFaceCount P

/-- The Euler characteristic `V − E + F`. -/
def eulerChar (P : FiniteCyclicPresentation) : ℤ :=
  (vertexCount P : ℤ) - P.edgeCount + P.faces.length

theorem rel_iff_exists_face (P : FiniteCyclicPresentation) {x y : P.Edge × Bool} :
    Corners.Rel P.faces x y ↔ ∃ f : P.Face, ∃ q ∈ Corners.pairs (P.boundary f),
      x = Corners.finish q.1 ∧ y = Corners.start q.2 := by
  constructor
  · rintro ⟨w, hw, q, hq, h⟩
    obtain ⟨f, rfl⟩ := List.mem_iff_get.mp hw
    exact ⟨f, q, hq, h⟩
  · rintro ⟨f, q, hq, h⟩
    exact ⟨P.boundary f, List.get_mem _ _, q, hq, h⟩

/-! ### Invariance under signed presentation isomorphisms -/

section SignedIso

variable {P Q : FiniteCyclicPresentation}

theorem rel_signedIso (e : SignedPresentationIso P Q) (x y : P.Edge × Bool) :
    Corners.Rel Q.faces (Corners.endMap e.edgeRelabeling x) (Corners.endMap e.edgeRelabeling y) ↔
      Corners.Rel P.faces x y := by
  rw [rel_iff_exists_face, rel_iff_exists_face]
  constructor
  · rintro ⟨g, q, hq, hx, hy⟩
    have hg : g = e.faceEquiv (e.faceEquiv.symm g) := (e.faceEquiv.apply_symm_apply g).symm
    rw [hg, Corners.mem_pairs_of_isRotated (e.boundary_rotated _), Corners.pairs_map,
      List.mem_map] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    refine ⟨e.faceEquiv.symm g, p, hp, ?_, ?_⟩
    · apply (Corners.endEquiv e.edgeRelabeling).injective
      simpa [Corners.endEquiv_apply, Corners.finish_mapDart] using hx
    · apply (Corners.endEquiv e.edgeRelabeling).injective
      simpa [Corners.endEquiv_apply, Corners.start_mapDart] using hy
  · rintro ⟨f, p, hp, rfl, rfl⟩
    refine ⟨e.faceEquiv f, Prod.map e.edgeRelabeling.mapDart e.edgeRelabeling.mapDart p, ?_,
      ?_, ?_⟩
    · rw [Corners.mem_pairs_of_isRotated (e.boundary_rotated f), Corners.pairs_map]
      exact List.mem_map_of_mem hp
    · simp [Corners.finish_mapDart]
    · simp [Corners.start_mapDart]

theorem natCard_quot_signedIso (e : SignedPresentationIso P Q) :
    Nat.card (Quot (Corners.Rel P.faces)) = Nat.card (Quot (Corners.Rel Q.faces)) := by
  refine natCard_quot_eq_of_maps (Corners.endEquiv e.edgeRelabeling)
    (Corners.endEquiv e.edgeRelabeling).symm ?_ ?_ ?_ ?_
  · intro x y h
    exact Relation.EqvGen.rel _ _ ((rel_signedIso e x y).mpr h)
  · intro u v h
    apply Relation.EqvGen.rel
    rw [← rel_signedIso e]
    simpa [← Corners.endEquiv_apply] using h
  · intro x
    rw [Equiv.symm_apply_apply]
    exact Relation.EqvGen.refl _
  · intro u
    rw [Equiv.apply_symm_apply]
    exact Relation.EqvGen.refl _

theorem emptyFaceCount_signedIso (e : SignedPresentationIso P Q) :
    emptyFaceCount P = emptyFaceCount Q := by
  refine Nat.card_congr (e.faceEquiv.subtypeEquiv fun f => ?_)
  have hlen := (e.boundary_rotated f).perm.length_eq
  rw [List.length_map] at hlen
  rw [← List.length_eq_zero_iff, ← List.length_eq_zero_iff, hlen]

theorem edgeCount_signedIso (e : SignedPresentationIso P Q) : P.edgeCount = Q.edgeCount := by
  simpa using Fintype.card_congr e.edgeRelabeling.edgeEquiv

theorem facesLength_signedIso (e : SignedPresentationIso P Q) :
    P.faces.length = Q.faces.length := by
  simpa using Fintype.card_congr e.faceEquiv

theorem eulerChar_signedIso (e : SignedPresentationIso P Q) : eulerChar P = eulerChar Q := by
  simp only [eulerChar, vertexCount, natCard_quot_signedIso e, emptyFaceCount_signedIso e,
    edgeCount_signedIso e, facesLength_signedIso e]

end SignedIso

/-! ### Invariance under unoriented presentation isomorphisms -/

section UnorientedIso

variable {P Q : FiniteCyclicPresentation}

theorem corner_inverseWord {α : Type*} {w : List (SignedDart α)} {x y : α × Bool} :
    (∃ q ∈ Corners.pairs (inverseWord w), x = Corners.finish q.1 ∧ y = Corners.start q.2) ↔
      ∃ q ∈ Corners.pairs w, y = Corners.finish q.1 ∧ x = Corners.start q.2 := by
  constructor
  · rintro ⟨q, hq, hx, hy⟩
    obtain ⟨p, hp, rfl⟩ := Corners.mem_pairs_inverseWord.mp hq
    exact ⟨p, hp, by simpa using hy, by simpa using hx⟩
  · rintro ⟨p, hp, hy, hx⟩
    exact ⟨(p.2.flip, p.1.flip), Corners.mem_pairs_inverseWord.mpr ⟨p, hp, rfl⟩,
      by simpa using hx, by simpa using hy⟩

/-- Corners of the oriented boundary of a face, in either orientation. -/
theorem corner_orientedBoundary (Q : FiniteCyclicPresentation) (g : Q.Face) (o : Bool)
    {u v : Q.Edge × Bool}
    (h : ∃ q ∈ Corners.pairs (Q.orientedBoundary ⟨g, o⟩),
      u = Corners.finish q.1 ∧ v = Corners.start q.2) :
    Corners.Rel Q.faces u v ∨ Corners.Rel Q.faces v u := by
  rw [rel_iff_exists_face, rel_iff_exists_face]
  cases o with
  | false => exact Or.inl ⟨g, h⟩
  | true =>
    simp only [orientedBoundary, ite_true] at h
    obtain ⟨q, hq, hv, hu⟩ := corner_inverseWord.mp h
    exact Or.inr ⟨g, q, hq, hv, hu⟩

theorem rel_unorientedIso_forward (e : UnorientedPresentationIso P Q) {x y : P.Edge × Bool}
    (h : Corners.Rel P.faces x y) :
    Corners.Rel Q.faces (Corners.endMap e.edgeRelabeling x) (Corners.endMap e.edgeRelabeling y) ∨
      Corners.Rel Q.faces (Corners.endMap e.edgeRelabeling y)
        (Corners.endMap e.edgeRelabeling x) := by
  obtain ⟨f, p, hp, rfl, rfl⟩ := (rel_iff_exists_face P).mp h
  apply corner_orientedBoundary Q (e.faceEquiv f) (e.reverseFace f)
  refine ⟨Prod.map e.edgeRelabeling.mapDart e.edgeRelabeling.mapDart p, ?_, ?_, ?_⟩
  · rw [Corners.mem_pairs_of_isRotated (e.boundary_rotated f), Corners.pairs_map]
    exact List.mem_map_of_mem hp
  · simp [Corners.finish_mapDart]
  · simp [Corners.start_mapDart]

theorem rel_unorientedIso_backward (e : UnorientedPresentationIso P Q) {u v : Q.Edge × Bool}
    (h : Corners.Rel Q.faces u v) :
    Corners.Rel P.faces ((Corners.endEquiv e.edgeRelabeling).symm u)
        ((Corners.endEquiv e.edgeRelabeling).symm v) ∨
      Corners.Rel P.faces ((Corners.endEquiv e.edgeRelabeling).symm v)
        ((Corners.endEquiv e.edgeRelabeling).symm u) := by
  obtain ⟨g, r, hr, rfl, rfl⟩ := (rel_iff_exists_face Q).mp h
  set f := e.faceEquiv.symm g
  have hg : g = e.faceEquiv f := (e.faceEquiv.apply_symm_apply g).symm
  have hrot := e.boundary_rotated f
  rw [← hg] at hrot
  have hback : ∀ {c d : SignedDart Q.Edge},
      (c, d) ∈ Corners.pairs (Q.orientedBoundary ⟨g, e.reverseFace f⟩) →
      ∃ p ∈ Corners.pairs (P.boundary f), c = e.edgeRelabeling.mapDart p.1 ∧
        d = e.edgeRelabeling.mapDart p.2 := by
    intro c d hcd
    rw [Corners.mem_pairs_of_isRotated hrot, Corners.pairs_map, List.mem_map] at hcd
    obtain ⟨p, hp, hpe⟩ := hcd
    simp only [Prod.map, Prod.mk.injEq] at hpe
    exact ⟨p, hp, hpe.1.symm, hpe.2.symm⟩
  have hsymm : ∀ a : P.Edge × Bool,
      (Corners.endEquiv e.edgeRelabeling).symm (Corners.endMap e.edgeRelabeling a) = a :=
    fun a => (Corners.endEquiv e.edgeRelabeling).symm_apply_apply a
  cases ho : e.reverseFace f with
  | false =>
    rw [ho] at hback
    obtain ⟨p, hp, hc, hd⟩ := hback (c := r.1) (d := r.2)
      (by simpa [orientedBoundary] using hr)
    left
    rw [hc, hd, Corners.finish_mapDart, Corners.start_mapDart, hsymm, hsymm]
    exact (rel_iff_exists_face P).mpr ⟨f, p, hp, rfl, rfl⟩
  | true =>
    rw [ho] at hback
    have hr' : (r.2.flip, r.1.flip) ∈
        Corners.pairs (Q.orientedBoundary ⟨g, true⟩) := by
      simp only [orientedBoundary, ite_true]
      exact Corners.mem_pairs_inverseWord.mpr ⟨r, hr, rfl⟩
    obtain ⟨p, hp, hc, hd⟩ := hback hr'
    right
    have h1 : Corners.start r.2 = Corners.endMap e.edgeRelabeling (Corners.finish p.1) := by
      rw [← Corners.finish_mapDart, ← hc, Corners.finish_flip]
    have h2 : Corners.finish r.1 = Corners.endMap e.edgeRelabeling (Corners.start p.2) := by
      rw [← Corners.start_mapDart, ← hd, Corners.start_flip]
    rw [h1, h2, hsymm, hsymm]
    exact (rel_iff_exists_face P).mpr ⟨f, p, hp, rfl, rfl⟩

theorem natCard_quot_unorientedIso (e : UnorientedPresentationIso P Q) :
    Nat.card (Quot (Corners.Rel P.faces)) = Nat.card (Quot (Corners.Rel Q.faces)) := by
  refine natCard_quot_eq_of_maps (Corners.endEquiv e.edgeRelabeling)
    (Corners.endEquiv e.edgeRelabeling).symm ?_ ?_ ?_ ?_
  · intro x y h
    rcases rel_unorientedIso_forward e h with h' | h'
    · exact Relation.EqvGen.rel _ _ h'
    · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h')
  · intro u v h
    rcases rel_unorientedIso_backward e h with h' | h'
    · exact Relation.EqvGen.rel _ _ h'
    · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h')
  · intro x
    rw [Equiv.symm_apply_apply]
    exact Relation.EqvGen.refl _
  · intro u
    rw [Equiv.apply_symm_apply]
    exact Relation.EqvGen.refl _

theorem emptyFaceCount_unorientedIso (e : UnorientedPresentationIso P Q) :
    emptyFaceCount P = emptyFaceCount Q := by
  refine Nat.card_congr (e.faceEquiv.subtypeEquiv fun f => ?_)
  have hlen := (e.boundary_rotated f).perm.length_eq
  rw [List.length_map] at hlen
  have hor : (Q.orientedBoundary ⟨e.faceEquiv f, e.reverseFace f⟩).length =
      (Q.boundary (e.faceEquiv f)).length := by
    cases e.reverseFace f <;> simp [orientedBoundary, inverseWord_length]
  rw [← List.length_eq_zero_iff, ← List.length_eq_zero_iff, hlen, hor]

theorem eulerChar_unorientedIso (e : UnorientedPresentationIso P Q) :
    eulerChar P = eulerChar Q := by
  have hE : P.edgeCount = Q.edgeCount := by simpa using Fintype.card_congr e.edgeRelabeling.edgeEquiv
  have hF : P.faces.length = Q.faces.length := by simpa using Fintype.card_congr e.faceEquiv
  simp only [eulerChar, vertexCount, natCard_quot_unorientedIso e, emptyFaceCount_unorientedIso e,
    hE, hF]

end UnorientedIso

/-! ### One extra isolated class -/

/-- The relation `r` on `Option α`, leaving `none` related to nothing. -/
def optionRel {α : Type*} (r : α → α → Prop) : Option α → Option α → Prop
  | some x, some y => r x y
  | _, _ => False

theorem natCard_quot_optionRel {α : Type*} [Finite α] (r : α → α → Prop) :
    Nat.card (Quot (optionRel r)) = Nat.card (Quot r) + 1 := by
  let e : Quot (optionRel r) ≃ Option (Quot r) :=
    { toFun := Quot.lift (fun o => o.map (Quot.mk r)) (by
        intro o o' h
        cases o <;> cases o'
        · exact h.elim
        · exact h.elim
        · exact h.elim
        · exact congrArg some (Quot.sound h))
      invFun := fun o => o.elim (Quot.mk _ none)
        (Quot.lift (fun x => Quot.mk (optionRel r) (some x)) fun x y h => Quot.sound h)
      left_inv := by
        intro q
        induction q using Quot.ind with
        | mk o => cases o <;> rfl
      right_inv := by
        intro o
        cases o with
        | none => rfl
        | some q =>
          induction q using Quot.ind with
          | mk x => rfl }
  rw [Nat.card_congr e, Finite.card_option]

/-! ### Invariance under P1 edge subdivision -/

section P1

variable (P : FiniteCyclicPresentation) (a : P.Edge)

/-- Old ends inside the expanded presentation: the head of `a` moves to the fresh subedge. -/
def p1End (x : P.Edge × Bool) : (P1.expand P a).Edge × Bool :=
  if x = (a, true) then (P1.freshEdge P.edgeCount, true) else (x.1.castSucc, x.2)

/-- The end of the first subedge at the new midpoint. -/
def p1Mid₁ : (P1.expand P a).Edge × Bool := (P1.firstSubedge a, true)

/-- The end of the fresh subedge at the new midpoint. -/
def p1Mid₂ : (P1.expand P a).Edge × Bool := (P1.freshEdge P.edgeCount, false)

/-- Ends of the expanded presentation read back in the old one; the midpoint goes to `none`. -/
def p1Back (u : (P1.expand P a).Edge × Bool) : Option (P.Edge × Bool) :=
  if u = p1Mid₁ P a ∨ u = p1Mid₂ P a then none
  else if h : u.1.val < P.edgeCount then some (⟨u.1.val, h⟩, u.2) else some (a, u.2)

theorem expandDart_ne_nil (d : SignedDart P.Edge) : P1.expandDart a d ≠ [] := by
  cases d with
  | pos e => by_cases h : e = a <;> simp [P1.expandDart, h]
  | neg e => by_cases h : e = a <;> simp [P1.expandDart, h]

theorem fresh_ne_castSucc (e : P.Edge) : P1.freshEdge P.edgeCount ≠ e.castSucc := by
  intro h
  have := congrArg Fin.val h
  simp [P1.freshEdge] at this
  omega

theorem finish_getLast_expandDart (d : SignedDart P.Edge) :
    Corners.finish ((P1.expandDart a d).getLast (expandDart_ne_nil P a d)) =
      p1End P a (Corners.finish d) := by
  cases d with
  | pos e => by_cases h : e = a <;> simp [P1.expandDart, h, p1End, Corners.finish]
  | neg e =>
    by_cases h : e = a
    · simp [P1.expandDart, h, p1End, Corners.finish, P1.firstSubedge]
    · simp [P1.expandDart, h, p1End, Corners.finish]

theorem start_head_expandDart (d : SignedDart P.Edge) :
    Corners.start ((P1.expandDart a d).head (expandDart_ne_nil P a d)) =
      p1End P a (Corners.start d) := by
  cases d with
  | pos e =>
    by_cases h : e = a
    · simp [P1.expandDart, h, p1End, Corners.start, P1.firstSubedge]
    · simp [P1.expandDart, h, p1End, Corners.start]
  | neg e => by_cases h : e = a <;> simp [P1.expandDart, h, p1End, Corners.start]

theorem p1Back_p1End (x : P.Edge × Bool) : p1Back P a (p1End P a x) = some x := by
  obtain ⟨e, b⟩ := x
  by_cases hx : (e, b) = (a, true)
  · rw [hx]
    have h1 : (P1.freshEdge P.edgeCount, true) ≠ p1Mid₁ P a := by
      simp [p1Mid₁, P1.firstSubedge, fresh_ne_castSucc]
    have h2 : (P1.freshEdge P.edgeCount, true) ≠ p1Mid₂ P a := by simp [p1Mid₂]
    have hp : p1End P a (a, true) = (P1.freshEdge P.edgeCount, true) := by simp [p1End]
    rw [hp, p1Back, if_neg (not_or.mpr ⟨h1, h2⟩), dif_neg (by simp [P1.freshEdge])]
  · have h1 : (e.castSucc, b) ≠ p1Mid₁ P a := by
      intro h
      simp only [p1Mid₁, P1.firstSubedge, Prod.mk.injEq, Fin.castSucc_inj] at h
      exact hx (by rw [h.1, h.2])
    have h2 : (e.castSucc, b) ≠ p1Mid₂ P a := by
      intro h
      simp only [p1Mid₂, Prod.mk.injEq] at h
      exact fresh_ne_castSucc P e h.1.symm
    simp [p1End, p1Back, hx, h1, h2]

theorem p1End_p1Back {u : (P1.expand P a).Edge × Bool} (h₁ : u ≠ p1Mid₁ P a)
    (h₂ : u ≠ p1Mid₂ P a) : (p1Back P a u).elim (p1Mid₁ P a) (p1End P a) = u := by
  obtain ⟨e', b⟩ := u
  by_cases hlt : e'.val < P.edgeCount
  · have hne : ((⟨e'.val, hlt⟩ : P.Edge), b) ≠ (a, true) := by
      intro h
      apply h₁
      simp only [Prod.mk.injEq] at h
      obtain ⟨h, rfl⟩ := h
      simp only [p1Mid₁, P1.firstSubedge, Prod.mk.injEq, and_true]
      ext
      simp [← h]
    simp [p1Back, h₁, h₂, hlt, p1End, hne]
  · have hlt' : e'.val < P.edgeCount + 1 := e'.isLt
    have he' : e' = P1.freshEdge P.edgeCount := by
      ext
      simp only [P1.freshEdge, Fin.val_last]
      omega
    subst he'
    have hb : b = true := by
      cases b
      · exact absurd rfl h₂
      · rfl
    subst hb
    simp [p1Back, h₁, h₂, hlt, p1End]

/-- Corners of the expanded presentation, read in the old one. -/
theorem rel_expand_cases {u v : (P1.expand P a).Edge × Bool}
    (h : Corners.Rel (P1.expand P a).faces u v) :
    (∃ x y, Corners.Rel P.faces x y ∧ u = p1End P a x ∧ v = p1End P a y) ∨
      ((u = p1Mid₁ P a ∨ u = p1Mid₂ P a) ∧ (v = p1Mid₁ P a ∨ v = p1Mid₂ P a)) := by
  obtain ⟨w', hw', q, hq, rfl, rfl⟩ := h
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hw'
  rw [P1.expandWord, Corners.mem_pairs_flatMap (expandDart_ne_nil P a)] at hq
  rcases hq with ⟨d, hd, hq⟩ | ⟨p, hp, rfl⟩
  · right
    cases d with
    | pos e =>
      by_cases he : e = a
      · subst he
        simp [P1.expandDart] at hq
        subst hq
        simp [p1Mid₁, p1Mid₂, Corners.finish, Corners.start, P1.firstSubedge]
      · simp [P1.expandDart, he] at hq
    | neg e =>
      by_cases he : e = a
      · subst he
        simp [P1.expandDart] at hq
        subst hq
        simp [p1Mid₁, p1Mid₂, Corners.finish, Corners.start, P1.firstSubedge]
      · simp [P1.expandDart, he] at hq
  · left
    exact ⟨Corners.finish p.1, Corners.start p.2, ⟨w, hw, p, hp, rfl, rfl⟩,
      finish_getLast_expandDart P a p.1, start_head_expandDart P a p.2⟩

theorem rel_expand_of_rel {x y : P.Edge × Bool} (h : Corners.Rel P.faces x y) :
    Corners.Rel (P1.expand P a).faces (p1End P a x) (p1End P a y) := by
  obtain ⟨w, hw, p, hp, rfl, rfl⟩ := h
  refine ⟨P1.expandWord a w, List.mem_map_of_mem hw,
    ((P1.expandDart a p.1).getLast (expandDart_ne_nil P a _),
      (P1.expandDart a p.2).head (expandDart_ne_nil P a _)), ?_,
    (finish_getLast_expandDart P a p.1).symm, (start_head_expandDart P a p.2).symm⟩
  rw [P1.expandWord, Corners.mem_pairs_flatMap (expandDart_ne_nil P a)]
  exact Or.inr ⟨p, hp, rfl⟩

theorem rel_expand_mid (ha : ∃ w ∈ P.faces, SignedDart.pos a ∈ w ∨ SignedDart.neg a ∈ w) :
    Relation.EqvGen (Corners.Rel (P1.expand P a).faces) (p1Mid₁ P a) (p1Mid₂ P a) := by
  obtain ⟨w, hw, hpos | hneg⟩ := ha
  · apply Relation.EqvGen.rel
    refine ⟨P1.expandWord a w, List.mem_map_of_mem hw,
      (SignedDart.pos (P1.firstSubedge a), SignedDart.pos (P1.freshEdge P.edgeCount)), ?_,
      rfl, rfl⟩
    rw [P1.expandWord, Corners.mem_pairs_flatMap (expandDart_ne_nil P a)]
    exact Or.inl ⟨_, hpos, by simp [P1.expandDart, Corners.lin]⟩
  · apply Relation.EqvGen.symm
    apply Relation.EqvGen.rel
    refine ⟨P1.expandWord a w, List.mem_map_of_mem hw,
      (SignedDart.neg (P1.freshEdge P.edgeCount), SignedDart.neg (P1.firstSubedge a)), ?_,
      rfl, rfl⟩
    rw [P1.expandWord, Corners.mem_pairs_flatMap (expandDart_ne_nil P a)]
    exact Or.inl ⟨_, hneg, by simp [P1.expandDart, Corners.lin]⟩

theorem natCard_quot_expand (ha : ∃ w ∈ P.faces, SignedDart.pos a ∈ w ∨ SignedDart.neg a ∈ w) :
    Nat.card (Quot (Corners.Rel (P1.expand P a).faces)) =
      Nat.card (Quot (Corners.Rel P.faces)) + 1 := by
  rw [← natCard_quot_optionRel]
  symm
  refine natCard_quot_eq_of_maps (fun o => o.elim (p1Mid₁ P a) (p1End P a)) (p1Back P a)
    ?_ ?_ ?_ ?_
  · intro o o' h
    cases o with
    | none => exact h.elim
    | some x =>
      cases o' with
      | none => exact h.elim
      | some y => exact Relation.EqvGen.rel _ _ (rel_expand_of_rel P a h)
  · intro u v h
    rcases rel_expand_cases P a h with ⟨x, y, hxy, rfl, rfl⟩ | ⟨hu, hv⟩
    · rw [p1Back_p1End, p1Back_p1End]
      exact Relation.EqvGen.rel _ _ hxy
    · have hnone : ∀ z, (z = p1Mid₁ P a ∨ z = p1Mid₂ P a) → p1Back P a z = none := by
        intro z hz
        simp [p1Back, hz]
      rw [hnone u hu, hnone v hv]
      exact Relation.EqvGen.refl _
  · intro o
    cases o with
    | none =>
      have : p1Back P a (p1Mid₁ P a) = none := by simp [p1Back]
      simp only [Option.elim, this]
      exact Relation.EqvGen.refl _
    | some x =>
      simp only [Option.elim, p1Back_p1End]
      exact Relation.EqvGen.refl _
  · intro u
    by_cases h₁ : u = p1Mid₁ P a
    · subst h₁
      have : p1Back P a (p1Mid₁ P a) = none := by simp [p1Back]
      rw [this]
      exact Relation.EqvGen.refl _
    by_cases h₂ : u = p1Mid₂ P a
    · subst h₂
      have : p1Back P a (p1Mid₂ P a) = none := by simp [p1Back]
      rw [this]
      exact rel_expand_mid P a ha
    rw [p1End_p1Back P a h₁ h₂]
    exact Relation.EqvGen.refl _

theorem expandWord_eq_nil_iff (w : List (SignedDart P.Edge)) :
    P1.expandWord a w = [] ↔ w = [] := by
  constructor
  · intro h
    cases w with
    | nil => rfl
    | cons d ds =>
      rw [P1.expandWord, List.flatMap_cons, List.append_eq_nil_iff] at h
      exact absurd h.1 (expandDart_ne_nil P a d)
  · rintro rfl
    rfl

theorem emptyFaceCount_expand : emptyFaceCount (P1.expand P a) = emptyFaceCount P := by
  symm
  refine Nat.card_congr ((P1.faceEquiv P a).subtypeEquiv fun f => ?_)
  have hb : (P1.expand P a).boundary (P1.faceEquiv P a f) = P1.expandWord a (P.boundary f) := by
    simp [FiniteCyclicPresentation.boundary, P1.faceEquiv]
  rw [hb, expandWord_eq_nil_iff]

theorem eulerChar_expand (ha : ∃ w ∈ P.faces, SignedDart.pos a ∈ w ∨ SignedDart.neg a ∈ w) :
    eulerChar (P1.expand P a) = eulerChar P := by
  simp only [eulerChar, vertexCount, natCard_quot_expand P a ha, emptyFaceCount_expand,
    P1.expand_edgeCount, List.length_map]
  push_cast
  ring

end P1

/-! ### Invariance under P2 face splitting -/

section P2

/-- Old ends inside an enlarged edge type. -/
def castEnd {n : ℕ} (x : Fin n × Bool) : Fin (n + 1) × Bool := (x.1.castSucc, x.2)

theorem finish_castSuccDart {n : ℕ} (d : SignedDart (Fin n)) :
    Corners.finish (P1.castSuccDart d) = castEnd (Corners.finish d) := by
  cases d <;> rfl

theorem start_castSuccDart {n : ℕ} (d : SignedDart (Fin n)) :
    Corners.start (P1.castSuccDart d) = castEnd (Corners.start d) := by
  cases d <;> rfl

theorem of_retainWord {n : ℕ} {w : List (SignedDart (Fin n))} {u v : Fin (n + 1) × Bool} :
    Corners.Of (P2.retainWord w) u v ↔
      ∃ x y, Corners.Of w x y ∧ u = castEnd x ∧ v = castEnd y := by
  simp only [Corners.Of, P2.retainWord, Corners.pairs_map, List.mem_map]
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl, rfl⟩
    exact ⟨_, _, ⟨q, hq, rfl, rfl⟩, finish_castSuccDart _, start_castSuccDart _⟩
  · rintro ⟨x, y, ⟨q, hq, rfl, rfl⟩, rfl, rfl⟩
    exact ⟨_, ⟨q, hq, rfl⟩, (finish_castSuccDart _).symm, (start_castSuccDart _).symm⟩

theorem ofLin_retainWord {n : ℕ} {w : List (SignedDart (Fin n))} {u v : Fin (n + 1) × Bool} :
    Corners.OfLin (P2.retainWord w) u v ↔
      ∃ x y, Corners.OfLin w x y ∧ u = castEnd x ∧ v = castEnd y := by
  simp only [Corners.OfLin, P2.retainWord, Corners.lin_map, List.mem_map]
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl, rfl⟩
    exact ⟨_, _, ⟨q, hq, rfl, rfl⟩, finish_castSuccDart _, start_castSuccDart _⟩
  · rintro ⟨x, y, ⟨q, hq, rfl, rfl⟩, rfl, rfl⟩
    exact ⟨_, ⟨q, hq, rfl⟩, (finish_castSuccDart _).symm, (start_castSuccDart _).symm⟩

theorem retainWord_ne_nil {n : ℕ} {w : List (SignedDart (Fin n))} (h : w ≠ []) :
    P2.retainWord w ≠ [] := by
  simpa [P2.retainWord] using h

theorem getLast_retainWord {n : ℕ} {w : List (SignedDart (Fin n))} (h : w ≠ []) :
    (P2.retainWord w).getLast (retainWord_ne_nil h) = P1.castSuccDart (w.getLast h) := by
  simp [P2.retainWord, List.getLast_map]

theorem head_retainWord {n : ℕ} {w : List (SignedDart (Fin n))} (h : w ≠ []) :
    (P2.retainWord w).head (retainWord_ne_nil h) = P1.castSuccDart (w.head h) := by
  simp [P2.retainWord, List.head_map]

theorem sOf_storedWord {α : Type*} (o : Bool) {w : List (SignedDart α)} {x y : α × Bool} :
    Corners.SOf (P2.storedWord o w) x y ↔ Corners.SOf w x y := by
  cases o
  · rfl
  · exact Corners.sOf_inverseWord

variable (P : FiniteCyclicPresentation) (cut : P2Cut P)

theorem mem_split_faces {w : List (SignedDart (Fin (P.edgeCount + 1)))} :
    w ∈ (P2.split P cut).faces ↔ w = P2.selectedBoundary P cut ∨ w = P2.rightBoundary P cut ∨
      ∃ f : P.Face, f ≠ cut.face.face ∧ w = P2.retainWord (P.boundary f) := by
  simp only [P2.split, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.lastCases with
    | last => simp [P2.faceWord]
    | cast f =>
      by_cases hf : f = cut.face.face
      · simp [P2.faceWord, hf]
      · simp only [P2.faceWord, Fin.lastCases_castSucc, hf, if_false]
        exact Or.inr (Or.inr ⟨f, hf, rfl⟩)
  · rintro (rfl | rfl | ⟨f, hf, rfl⟩)
    · exact ⟨Fin.castSucc cut.face.face, by simp [P2.faceWord]⟩
    · exact ⟨Fin.last _, by simp [P2.faceWord]⟩
    · exact ⟨Fin.castSucc f, by simp [P2.faceWord, hf]⟩

theorem sOf_cut_face {x y : P.Edge × Bool} :
    Corners.SOf (P.boundary cut.face.face) x y ↔ Corners.SOf (cut.left ++ cut.right) x y := by
  rw [Corners.sOf_isRotated cut.boundary_rotated]
  cases ho : cut.face.orientation
  · simp [orientedBoundary, ho]
  · simp only [orientedBoundary, ho, if_true]
    exact Corners.sOf_inverseWord.symm

variable {P cut} (hne : cut.left ++ cut.right ≠ [])

include hne in
theorem right_append_left_ne_nil : cut.right ++ cut.left ≠ [] := by
  intro h
  apply hne
  rw [List.append_eq_nil_iff] at h ⊢
  exact ⟨h.2, h.1⟩

/-- The dart before the first cut corner. -/
def cutBefore₁ : P.Dart := (cut.right ++ cut.left).getLast (right_append_left_ne_nil hne)
/-- The dart after the first cut corner. -/
def cutAfter₁ : P.Dart := (cut.right ++ cut.left).head (right_append_left_ne_nil hne)
/-- The dart before the second cut corner. -/
def cutBefore₂ : P.Dart := (cut.left ++ cut.right).getLast hne
/-- The dart after the second cut corner. -/
def cutAfter₂ : P.Dart := (cut.left ++ cut.right).head hne

/-- Corners of the cut face: those inside `left`, inside `right`, and the two cut corners. -/
theorem of_cut_iff {x y : P.Edge × Bool} :
    Corners.Of (cut.left ++ cut.right) x y ↔
      Corners.OfLin cut.left x y ∨ Corners.OfLin cut.right x y ∨
        (x = Corners.finish (cutBefore₁ hne) ∧ y = Corners.start (cutAfter₁ hne)) ∨
        (x = Corners.finish (cutBefore₂ hne) ∧ y = Corners.start (cutAfter₂ hne)) := by
  rcases Corners.nil_or_ne_nil cut.left with hL | hL <;>
    rcases Corners.nil_or_ne_nil cut.right with hR | hR
  · exact absurd (by simp [hL, hR]) hne
  · have hb₁ : cutBefore₁ hne = cut.right.getLast hR := by simp [cutBefore₁, hL]
    have ha₁ : cutAfter₁ hne = cut.right.head hR := by simp [cutAfter₁, hL]
    have hb₂ : cutBefore₂ hne = cut.right.getLast hR := by simp [cutBefore₂, hL]
    have ha₂ : cutAfter₂ hne = cut.right.head hR := by simp [cutAfter₂, hL]
    rw [hb₁, ha₁, hb₂, ha₂]
    simp only [hL, List.nil_append, Corners.of_iff_ofLin_or_wrap hR]
    have : ¬ Corners.OfLin ([] : List P.Dart) x y := by simp [Corners.OfLin]
    tauto
  · have hb₁ : cutBefore₁ hne = cut.left.getLast hL := by simp [cutBefore₁, hR]
    have ha₁ : cutAfter₁ hne = cut.left.head hL := by simp [cutAfter₁, hR]
    have hb₂ : cutBefore₂ hne = cut.left.getLast hL := by simp [cutBefore₂, hR]
    have ha₂ : cutAfter₂ hne = cut.left.head hL := by simp [cutAfter₂, hR]
    rw [hb₁, ha₁, hb₂, ha₂]
    simp only [hR, List.append_nil, Corners.of_iff_ofLin_or_wrap hL]
    have : ¬ Corners.OfLin ([] : List P.Dart) x y := by simp [Corners.OfLin]
    tauto
  · have hb₁ : cutBefore₁ hne = cut.left.getLast hL := by
      simp [cutBefore₁, List.getLast_append_of_ne_nil _ hL]
    have ha₁ : cutAfter₁ hne = cut.right.head hR := by
      simp [cutAfter₁, List.head_append_of_ne_nil hR]
    have hb₂ : cutBefore₂ hne = cut.right.getLast hR := by
      simp [cutBefore₂, List.getLast_append_of_ne_nil _ hR]
    have ha₂ : cutAfter₂ hne = cut.left.head hL := by
      simp [cutAfter₂, List.head_append_of_ne_nil hL]
    rw [hb₁, ha₁, hb₂, ha₂, Corners.of_append hL hR]
    tauto

/-- The fresh edge's tail and head. -/
abbrev freshTail (P : FiniteCyclicPresentation) : Fin (P.edgeCount + 1) × Bool :=
  (P2.freshEdge P, false)
abbrev freshHead (P : FiniteCyclicPresentation) : Fin (P.edgeCount + 1) × Bool :=
  (P2.freshEdge P, true)

/-- Corners of the first child word `left ++ [x]`. -/
theorem of_selected {u v : Fin (P.edgeCount + 1) × Bool}
    (h : Corners.Of (P2.selectedOrientedBoundary P cut) u v) :
    (∃ x y, Corners.OfLin cut.left x y ∧ u = castEnd x ∧ v = castEnd y) ∨
      (∃ hL : cut.left ≠ [], u = castEnd (Corners.finish (cut.left.getLast hL)) ∧
        v = freshTail P) ∨
      (∃ hL : cut.left ≠ [], u = freshHead P ∧ v = castEnd (Corners.start (cut.left.head hL))) ∨
      (cut.left = [] ∧ u = freshHead P ∧ v = freshTail P) := by
  rcases Corners.nil_or_ne_nil cut.left with hL | hL
  · simp only [P2.selectedOrientedBoundary, hL, P2.retainWord, List.map_nil, List.nil_append,
      Corners.of_singleton] at h
    exact Or.inr (Or.inr (Or.inr ⟨hL, h.1, h.2⟩))
  · have hL' := retainWord_ne_nil hL
    rw [P2.selectedOrientedBoundary, Corners.of_append hL' (List.cons_ne_nil _ [])] at h
    rcases h with h | ⟨hu, hv⟩ | h | ⟨hu, hv⟩
    · exact Or.inl (ofLin_retainWord.mp h)
    · refine Or.inr (Or.inl ⟨hL, ?_, ?_⟩)
      · rw [hu, getLast_retainWord hL, finish_castSuccDart]
      · rw [hv]
        rfl
    · exact absurd h (Corners.ofLin_singleton _)
    · refine Or.inr (Or.inr (Or.inl ⟨hL, ?_, ?_⟩))
      · rw [hu]
        rfl
      · rw [hv, head_retainWord hL, start_castSuccDart]

/-- Corners of the second child word `x⁻¹ :: right`. -/
theorem of_rightChild {u v : Fin (P.edgeCount + 1) × Bool}
    (h : Corners.Of (P2.rightOrientedBoundary P cut) u v) :
    (∃ x y, Corners.OfLin cut.right x y ∧ u = castEnd x ∧ v = castEnd y) ∨
      (∃ hR : cut.right ≠ [], u = freshTail P ∧ v = castEnd (Corners.start (cut.right.head hR))) ∨
      (∃ hR : cut.right ≠ [], u = castEnd (Corners.finish (cut.right.getLast hR)) ∧
        v = freshHead P) ∨
      (cut.right = [] ∧ u = freshTail P ∧ v = freshHead P) := by
  rcases Corners.nil_or_ne_nil cut.right with hR | hR
  · simp only [P2.rightOrientedBoundary, hR, P2.retainWord, List.map_nil,
      Corners.of_singleton] at h
    exact Or.inr (Or.inr (Or.inr ⟨hR, h.1, h.2⟩))
  · have hR' := retainWord_ne_nil hR
    rw [P2.rightOrientedBoundary, ← List.singleton_append,
      Corners.of_append (List.cons_ne_nil _ []) hR'] at h
    rcases h with h | ⟨hu, hv⟩ | h | ⟨hu, hv⟩
    · exact absurd h (Corners.ofLin_singleton _)
    · refine Or.inr (Or.inl ⟨hR, ?_, ?_⟩)
      · rw [hu]
        rfl
      · rw [hv, head_retainWord hR, start_castSuccDart]
    · exact Or.inl (ofLin_retainWord.mp h)
    · refine Or.inr (Or.inr (Or.inl ⟨hR, ?_, ?_⟩))
      · rw [hu, getLast_retainWord hR, finish_castSuccDart]
      · rw [hv]
        rfl

/-- The relation of the split presentation contains the corners of both children, in either
direction. -/
theorem eqvGen_of_selected {u v : Fin (P.edgeCount + 1) × Bool}
    (h : Corners.Of (P2.selectedOrientedBoundary P cut) u v) :
    Relation.EqvGen (Corners.Rel (P2.split P cut).faces) u v := by
  have hs : Corners.SOf (P2.selectedBoundary P cut) u v :=
    (sOf_storedWord cut.face.orientation).mpr (Or.inl h)
  have hmem : P2.selectedBoundary P cut ∈ (P2.split P cut).faces :=
    (mem_split_faces P cut).mpr (Or.inl rfl)
  rcases hs with h' | h'
  · exact Relation.EqvGen.rel _ _ ⟨_, hmem, h'⟩
  · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨_, hmem, h'⟩)

theorem eqvGen_of_rightChild {u v : Fin (P.edgeCount + 1) × Bool}
    (h : Corners.Of (P2.rightOrientedBoundary P cut) u v) :
    Relation.EqvGen (Corners.Rel (P2.split P cut).faces) u v := by
  have hs : Corners.SOf (P2.rightBoundary P cut) u v :=
    (sOf_storedWord cut.face.orientation).mpr (Or.inl h)
  have hmem : P2.rightBoundary P cut ∈ (P2.split P cut).faces :=
    (mem_split_faces P cut).mpr (Or.inr (Or.inl rfl))
  rcases hs with h' | h'
  · exact Relation.EqvGen.rel _ _ ⟨_, hmem, h'⟩
  · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨_, hmem, h'⟩)

/-! Corners of the children that pass through the fresh edge. -/

theorem selected_last (hL : cut.left ≠ []) :
    Corners.Of (P2.selectedOrientedBoundary P cut)
      (castEnd (Corners.finish (cut.left.getLast hL))) (freshTail P) := by
  rw [P2.selectedOrientedBoundary,
    Corners.of_append (retainWord_ne_nil hL) (List.cons_ne_nil _ [])]
  refine Or.inr (Or.inl ⟨?_, rfl⟩)
  rw [getLast_retainWord hL, finish_castSuccDart]

theorem selected_head (hL : cut.left ≠ []) :
    Corners.Of (P2.selectedOrientedBoundary P cut)
      (freshHead P) (castEnd (Corners.start (cut.left.head hL))) := by
  rw [P2.selectedOrientedBoundary,
    Corners.of_append (retainWord_ne_nil hL) (List.cons_ne_nil _ [])]
  refine Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))
  rw [head_retainWord hL, start_castSuccDart]

theorem selected_monogon (hL : cut.left = []) :
    Corners.Of (P2.selectedOrientedBoundary P cut) (freshHead P) (freshTail P) := by
  simp only [P2.selectedOrientedBoundary, hL, P2.retainWord, List.map_nil, List.nil_append,
    Corners.of_singleton]
  exact ⟨rfl, rfl⟩

theorem rightChild_head (hR : cut.right ≠ []) :
    Corners.Of (P2.rightOrientedBoundary P cut)
      (freshTail P) (castEnd (Corners.start (cut.right.head hR))) := by
  rw [P2.rightOrientedBoundary, ← List.singleton_append,
    Corners.of_append (List.cons_ne_nil _ []) (retainWord_ne_nil hR)]
  refine Or.inr (Or.inl ⟨rfl, ?_⟩)
  rw [head_retainWord hR, start_castSuccDart]

theorem rightChild_last (hR : cut.right ≠ []) :
    Corners.Of (P2.rightOrientedBoundary P cut)
      (castEnd (Corners.finish (cut.right.getLast hR))) (freshHead P) := by
  rw [P2.rightOrientedBoundary, ← List.singleton_append,
    Corners.of_append (List.cons_ne_nil _ []) (retainWord_ne_nil hR)]
  refine Or.inr (Or.inr (Or.inr ⟨?_, rfl⟩))
  rw [getLast_retainWord hR, finish_castSuccDart]

theorem rightChild_monogon (hR : cut.right = []) :
    Corners.Of (P2.rightOrientedBoundary P cut) (freshTail P) (freshHead P) := by
  simp only [P2.rightOrientedBoundary, hR, P2.retainWord, List.map_nil, Corners.of_singleton]
  exact ⟨rfl, rfl⟩

/-! The four chains through the fresh edge. -/

theorem chain_before₁ :
    Relation.EqvGen (Corners.Rel (P2.split P cut).faces)
      (castEnd (Corners.finish (cutBefore₁ hne))) (freshTail P) := by
  rcases Corners.nil_or_ne_nil cut.left with hL | hL
  · have hR : cut.right ≠ [] := by simpa [hL] using hne
    have hb : cutBefore₁ hne = cut.right.getLast hR := by simp [cutBefore₁, hL]
    rw [hb]
    exact Relation.EqvGen.trans _ _ _ (eqvGen_of_rightChild (rightChild_last hR))
      (eqvGen_of_selected (selected_monogon hL))
  · have hb : cutBefore₁ hne = cut.left.getLast hL := by
      simp [cutBefore₁, List.getLast_append_of_ne_nil _ hL]
    rw [hb]
    exact eqvGen_of_selected (selected_last hL)

theorem chain_after₁ :
    Relation.EqvGen (Corners.Rel (P2.split P cut).faces)
      (castEnd (Corners.start (cutAfter₁ hne))) (freshTail P) := by
  rcases Corners.nil_or_ne_nil cut.right with hR | hR
  · have hL : cut.left ≠ [] := by simpa [hR] using hne
    have ha : cutAfter₁ hne = cut.left.head hL := by simp [cutAfter₁, hR]
    rw [ha]
    exact Relation.EqvGen.symm _ _ (Relation.EqvGen.trans _ _ _
      (eqvGen_of_rightChild (rightChild_monogon hR)) (eqvGen_of_selected (selected_head hL)))
  · have ha : cutAfter₁ hne = cut.right.head hR := by
      simp [cutAfter₁, List.head_append_of_ne_nil hR]
    rw [ha]
    exact Relation.EqvGen.symm _ _ (eqvGen_of_rightChild (rightChild_head hR))

theorem chain_before₂ :
    Relation.EqvGen (Corners.Rel (P2.split P cut).faces)
      (castEnd (Corners.finish (cutBefore₂ hne))) (freshHead P) := by
  rcases Corners.nil_or_ne_nil cut.right with hR | hR
  · have hL : cut.left ≠ [] := by simpa [hR] using hne
    have hb : cutBefore₂ hne = cut.left.getLast hL := by simp [cutBefore₂, hR]
    rw [hb]
    exact Relation.EqvGen.trans _ _ _ (eqvGen_of_selected (selected_last hL))
      (eqvGen_of_rightChild (rightChild_monogon hR))
  · have hb : cutBefore₂ hne = cut.right.getLast hR := by
      simp [cutBefore₂, List.getLast_append_of_ne_nil _ hR]
    rw [hb]
    exact eqvGen_of_rightChild (rightChild_last hR)

theorem chain_after₂ :
    Relation.EqvGen (Corners.Rel (P2.split P cut).faces)
      (castEnd (Corners.start (cutAfter₂ hne))) (freshHead P) := by
  rcases Corners.nil_or_ne_nil cut.left with hL | hL
  · have hR : cut.right ≠ [] := by simpa [hL] using hne
    have ha : cutAfter₂ hne = cut.right.head hR := by simp [cutAfter₂, hL]
    rw [ha]
    exact Relation.EqvGen.symm _ _ (Relation.EqvGen.trans _ _ _
      (eqvGen_of_selected (selected_monogon hL)) (eqvGen_of_rightChild (rightChild_head hR)))
  · have ha : cutAfter₂ hne = cut.left.head hL := by
      simp [cutAfter₂, List.head_append_of_ne_nil hL]
    rw [ha]
    exact Relation.EqvGen.symm _ _ (eqvGen_of_selected (selected_head hL))

/-- Ends of the split presentation read back in the old one. -/
def p2Back (u : Fin (P.edgeCount + 1) × Bool) : P.Edge × Bool :=
  if h : u.1.val < P.edgeCount then (⟨u.1.val, h⟩, u.2)
  else if u.2 then Corners.finish (cutBefore₂ hne) else Corners.finish (cutBefore₁ hne)

theorem p2Back_castEnd (x : P.Edge × Bool) : p2Back hne (castEnd x) = x := by
  obtain ⟨e, b⟩ := x
  simp [p2Back, castEnd]

theorem p2Back_freshTail : p2Back hne (freshTail P) = Corners.finish (cutBefore₁ hne) := by
  simp [p2Back, P2.freshEdge, P1.freshEdge]

theorem p2Back_freshHead : p2Back hne (freshHead P) = Corners.finish (cutBefore₂ hne) := by
  simp [p2Back, P2.freshEdge, P1.freshEdge]

/-- An old corner of the cut face, as a relation of the old presentation. -/
theorem eqvGen_old_of_cut {x y : P.Edge × Bool} (h : Corners.Of (cut.left ++ cut.right) x y) :
    Relation.EqvGen (Corners.Rel P.faces) x y := by
  have hs : Corners.SOf (P.boundary cut.face.face) x y :=
    (sOf_cut_face P cut).mpr (Or.inl h)
  have hmem : P.boundary cut.face.face ∈ P.faces := List.get_mem _ _
  rcases hs with h' | h'
  · exact Relation.EqvGen.rel _ _ ⟨_, hmem, h'⟩
  · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨_, hmem, h'⟩)

include hne in
theorem natCard_quot_split :
    Nat.card (Quot (Corners.Rel P.faces)) = Nat.card (Quot (Corners.Rel (P2.split P cut).faces)) := by
  refine natCard_quot_eq_of_maps castEnd (p2Back hne) ?_ ?_ ?_ ?_
  · -- old corners become relations of the split presentation
    intro x y h
    obtain ⟨w, hw, hxy⟩ := h
    obtain ⟨f, rfl⟩ := List.mem_iff_get.mp hw
    by_cases hf : f = cut.face.face
    · subst hf
      have hs : Corners.SOf (cut.left ++ cut.right) x y :=
        (sOf_cut_face P cut).mp (Or.inl hxy)
      have key : ∀ {a b : P.Edge × Bool}, Corners.Of (cut.left ++ cut.right) a b →
          Relation.EqvGen (Corners.Rel (P2.split P cut).faces) (castEnd a) (castEnd b) := by
        intro a b hab
        rcases (of_cut_iff hne).mp hab with hl | hr | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · apply eqvGen_of_selected
          rw [P2.selectedOrientedBoundary]
          exact Corners.of_of_ofLin (Corners.ofLin_of_ofLin_append_left
            (ofLin_retainWord.mpr ⟨a, b, hl, rfl, rfl⟩))
        · apply eqvGen_of_rightChild
          rw [P2.rightOrientedBoundary, ← List.singleton_append]
          exact Corners.of_of_ofLin (Corners.ofLin_of_ofLin_append_right
            (ofLin_retainWord.mpr ⟨a, b, hr, rfl, rfl⟩))
        · exact Relation.EqvGen.trans _ _ _ (chain_before₁ hne)
            (Relation.EqvGen.symm _ _ (chain_after₁ hne))
        · exact Relation.EqvGen.trans _ _ _ (chain_before₂ hne)
            (Relation.EqvGen.symm _ _ (chain_after₂ hne))
      rcases hs with h' | h'
      · exact key h'
      · exact Relation.EqvGen.symm _ _ (key h')
    · apply Relation.EqvGen.rel
      refine ⟨P2.retainWord (P.faces.get f), (mem_split_faces P cut).mpr
        (Or.inr (Or.inr ⟨f, hf, rfl⟩)), ?_⟩
      exact of_retainWord.mpr ⟨x, y, hxy, rfl, rfl⟩
  · -- corners of the split presentation read back
    intro u v h
    obtain ⟨w, hw, huv⟩ := h
    have back : ∀ {a b : P.Edge × Bool}, Corners.OfLin cut.left a b ∨ Corners.OfLin cut.right a b →
        Relation.EqvGen (Corners.Rel P.faces) (p2Back hne (castEnd a)) (p2Back hne (castEnd b)) := by
      intro a b hab
      rw [p2Back_castEnd, p2Back_castEnd]
      exact eqvGen_old_of_cut ((of_cut_iff hne).mpr (by tauto))
    have selected : ∀ {a b}, Corners.Of (P2.selectedOrientedBoundary P cut) a b →
        Relation.EqvGen (Corners.Rel P.faces) (p2Back hne a) (p2Back hne b) := by
      intro a b hab
      rcases of_selected hab with ⟨x, y, hl, rfl, rfl⟩ | ⟨hL, rfl, rfl⟩ | ⟨hL, rfl, rfl⟩ |
          ⟨hL, rfl, rfl⟩
      · exact back (Or.inl hl)
      · rw [p2Back_castEnd, p2Back_freshTail]
        have hb : cutBefore₁ hne = cut.left.getLast hL := by
          simp [cutBefore₁, List.getLast_append_of_ne_nil _ hL]
        rw [hb]
        exact Relation.EqvGen.refl _
      · rw [p2Back_castEnd, p2Back_freshHead]
        have ha : cutAfter₂ hne = cut.left.head hL := by
          simp [cutAfter₂, List.head_append_of_ne_nil hL]
        rw [← ha]
        exact eqvGen_old_of_cut ((of_cut_iff hne).mpr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
      · rw [p2Back_freshHead, p2Back_freshTail]
        have h₁ : cutBefore₁ hne = cutBefore₂ hne := by simp [cutBefore₁, cutBefore₂, hL]
        rw [h₁]
        exact Relation.EqvGen.refl _
    have rightChild : ∀ {a b}, Corners.Of (P2.rightOrientedBoundary P cut) a b →
        Relation.EqvGen (Corners.Rel P.faces) (p2Back hne a) (p2Back hne b) := by
      intro a b hab
      rcases of_rightChild hab with ⟨x, y, hr, rfl, rfl⟩ | ⟨hR, rfl, rfl⟩ | ⟨hR, rfl, rfl⟩ |
          ⟨hR, rfl, rfl⟩
      · exact back (Or.inr hr)
      · rw [p2Back_castEnd, p2Back_freshTail]
        have ha : cutAfter₁ hne = cut.right.head hR := by
          simp [cutAfter₁, List.head_append_of_ne_nil hR]
        rw [← ha]
        exact eqvGen_old_of_cut ((of_cut_iff hne).mpr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
      · rw [p2Back_castEnd, p2Back_freshHead]
        have hb : cutBefore₂ hne = cut.right.getLast hR := by
          simp [cutBefore₂, List.getLast_append_of_ne_nil _ hR]
        rw [hb]
        exact Relation.EqvGen.refl _
      · rw [p2Back_freshTail, p2Back_freshHead]
        have h₁ : cutBefore₁ hne = cutBefore₂ hne := by simp [cutBefore₁, cutBefore₂, hR]
        rw [h₁]
        exact Relation.EqvGen.refl _
    rcases (mem_split_faces P cut).mp hw with rfl | rfl | ⟨f, hf, rfl⟩
    · have hs := (sOf_storedWord cut.face.orientation).mp (Or.inl huv)
      rcases hs with h' | h'
      · exact selected h'
      · exact Relation.EqvGen.symm _ _ (selected h')
    · have hs := (sOf_storedWord cut.face.orientation).mp (Or.inl huv)
      rcases hs with h' | h'
      · exact rightChild h'
      · exact Relation.EqvGen.symm _ _ (rightChild h')
    · obtain ⟨x, y, hxy, rfl, rfl⟩ := of_retainWord.mp huv
      rw [p2Back_castEnd, p2Back_castEnd]
      exact Relation.EqvGen.rel _ _ ⟨_, List.get_mem _ _, hxy⟩
  · intro x
    rw [p2Back_castEnd]
    exact Relation.EqvGen.refl _
  · intro u
    obtain ⟨e', b⟩ := u
    by_cases hlt : e'.val < P.edgeCount
    · have : castEnd (p2Back hne (e', b)) = (e', b) := by
        simp [p2Back, hlt, castEnd]
      rw [this]
      exact Relation.EqvGen.refl _
    · have hlt' : e'.val < P.edgeCount + 1 := e'.isLt
      have he' : e' = P2.freshEdge P := by
        ext
        simp only [P2.freshEdge, P1.freshEdge, Fin.val_last]
        omega
      subst he'
      cases b
      · rw [show ((P2.freshEdge P, false) : Fin (P.edgeCount + 1) × Bool) = freshTail P from rfl,
          p2Back_freshTail]
        exact chain_before₁ hne
      · rw [show ((P2.freshEdge P, true) : Fin (P.edgeCount + 1) × Bool) = freshHead P from rfl,
          p2Back_freshHead]
        exact chain_before₂ hne

include hne in
theorem emptyFaceCount_split : emptyFaceCount (P2.split P cut) = emptyFaceCount P := by
  have hface : P.boundary cut.face.face ≠ [] := by
    intro h
    have hlen := cut.boundary_rotated.perm.length_eq
    rw [P.orientedBoundary_length, h, List.length_nil] at hlen
    exact hne (List.eq_nil_of_length_eq_zero hlen.symm)
  have hsel : P2.selectedBoundary P cut ≠ [] := by
    cases ho : cut.face.orientation <;>
      simp [P2.selectedBoundary, P2.storedWord, P2.selectedOrientedBoundary, ho, inverseWord]
  have hright : P2.rightBoundary P cut ≠ [] := by
    cases ho : cut.face.orientation <;>
      simp [P2.rightBoundary, P2.storedWord, P2.rightOrientedBoundary, ho, inverseWord]
  have hret : ∀ f : P.Face, P2.retainWord (P.boundary f) = [] ↔ P.boundary f = [] := by
    intro f
    simp [P2.retainWord]
  let φ : {f : P.Face // P.boundary f = []} →
      {q : (P2.split P cut).Face // (P2.split P cut).boundary q = []} := fun f =>
    ⟨P2.oldFace P cut f.1, by
      have hf : f.1 ≠ cut.face.face := fun h => hface (h ▸ f.2)
      rw [P2.split_boundary_old_of_ne P cut hf, hret]
      exact f.2⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨f, hf⟩ ⟨f', hf'⟩ h
      simp only [φ, Subtype.mk.injEq, P2.oldFace] at h
      exact Subtype.ext (Fin.castSucc_injective _ ((P2.faceEquiv P cut).injective h))
    · rintro ⟨q, hq⟩
      rcases P2.face_cases P cut q with ⟨f, rfl⟩ | rfl
      · by_cases hf : f = cut.face.face
        · subst hf
          rw [P2.split_boundary_selected] at hq
          exact absurd hq hsel
        · rw [P2.split_boundary_old_of_ne P cut hf, hret] at hq
          exact ⟨⟨f, hq⟩, rfl⟩
      · rw [P2.split_boundary_right] at hq
        exact absurd hq hright
  exact (Nat.card_congr (Equiv.ofBijective φ hφ)).symm

include hne in
theorem eulerChar_split : eulerChar (P2.split P cut) = eulerChar P := by
  have h1 := natCard_quot_split hne
  have h2 := emptyFaceCount_split hne
  have h3 : (P2.split P cut).faces.length = P.faces.length + 1 := P2.split_faces_length P cut
  have h4 : (P2.split P cut).edgeCount = P.edgeCount + 1 := rfl
  unfold eulerChar vertexCount
  rw [← h1, h2, h3, h4]
  push_cast
  ring

end P2

/-! ### Invariance along Lean Pool's normalization -/

section Chains

theorem occurs_of_isSurfaceValid {P : FiniteCyclicPresentation} (hP : P.IsSurfaceValid)
    (a : P.Edge) : ∃ w ∈ P.faces, SignedDart.pos a ∈ w ∨ SignedDart.neg a ∈ w := by
  have hm : 1 ≤ P.edgeMultiplicity a := by
    rcases hP.2.2.2 a with h | h <;> omega
  obtain ⟨f, hf⟩ : ∃ f : P.Face, 0 < P.faceEdgeMultiplicity f a := by
    by_contra hcon
    push_neg at hcon
    have h0 : P.edgeMultiplicity a = 0 :=
      Finset.sum_eq_zero fun f _ => Nat.le_zero.mp (hcon f)
    omega
  have hmem : a ∈ (P.boundary f).map edgeOfDart := List.count_pos_iff.mp hf
  obtain ⟨d, hd, hda⟩ := List.mem_map.mp hmem
  refine ⟨P.boundary f, List.get_mem _ _, ?_⟩
  cases d with
  | pos e =>
    have : e = a := hda
    exact Or.inl (this ▸ hd)
  | neg e =>
    have : e = a := hda
    exact Or.inr (this ▸ hd)

theorem cut_ne_nil {P : FiniteCyclicPresentation} (hP : P.IsSurfaceValid) (cut : P2Cut P) :
    cut.left ++ cut.right ≠ [] := by
  intro h
  have hlen := cut.boundary_rotated.perm.length_eq
  rw [P.orientedBoundary_length, h, List.length_nil] at hlen
  exact hP.2.1 cut.face.face (List.eq_nil_of_length_eq_zero hlen)

theorem eulerChar_subdivisionStep {P Q : FiniteCyclicPresentation} (h : SubdivisionStep P Q)
    (hP : P.IsSurfaceValid) : eulerChar P = eulerChar Q := by
  rcases h with h | h | h
  · obtain ⟨e⟩ := h
    exact eulerChar_signedIso e
  · obtain ⟨a, he⟩ := h
    obtain ⟨e⟩ := he
    rw [← eulerChar_signedIso e, eulerChar_expand P a (occurs_of_isSurfaceValid hP a)]
  · obtain ⟨cut, -, he⟩ := h
    obtain ⟨e⟩ := he
    rw [← eulerChar_signedIso e, eulerChar_split (cut_ne_nil hP cut)]

theorem eulerChar_subdivides {P Q : FiniteCyclicPresentation} (h : Subdivides P Q)
    (hP : P.IsSurfaceValid) : eulerChar P = eulerChar Q := by
  induction h with
  | refl => rfl
  | tail hPR hstep ih =>
    exact ih.trans (eulerChar_subdivisionStep hstep (Subdivides.isSurfaceValid hPR hP))

theorem eulerChar_hasCommonSubdivision {P Q : FiniteCyclicPresentation}
    (h : HasCommonSubdivision P Q) (hP : P.IsSurfaceValid) (hQ : Q.IsSurfaceValid) :
    eulerChar P = eulerChar Q := by
  obtain ⟨R, hPR, hQR⟩ := h
  rw [eulerChar_subdivides hPR hP, eulerChar_subdivides hQR hQ]

theorem eulerChar_normalizationStep {P Q : ValidPresentation} (h : NormalizationStep P Q) :
    eulerChar P.presentation = eulerChar Q.presentation := by
  cases h with
  | commonSubdivision h => exact eulerChar_hasCommonSubdivision h P.valid Q.valid
  | unoriented h =>
    rcases h with h | h
    · obtain ⟨e⟩ := h
      exact eulerChar_unorientedIso e
    · obtain ⟨e⟩ := h
      exact (eulerChar_unorientedIso e).symm
  | oneSidedP2 cut _ => exact (eulerChar_split (cut_ne_nil P.valid cut)).symm

/-- The Euler characteristic is constant along Lean Pool's normalization. -/
theorem eulerChar_normalizationEquivalent {P Q : ValidPresentation}
    (h : NormalizationEquivalent P Q) : eulerChar P.presentation = eulerChar Q.presentation := by
  unfold NormalizationEquivalent at h
  induction h with
  | rel _ _ h => exact eulerChar_normalizationStep h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end Chains

/-! ### Euler characteristics of the canonical presentations -/

section Canonical

open NormalForm

theorem finish_mapEquiv {α β : Type*} (e : α ≃ β) (d : SignedDart α) :
    Corners.finish (SignedDart.mapEquiv e d) = Prod.map e id (Corners.finish d) := by
  cases d <;> rfl

theorem start_mapEquiv {α β : Type*} (e : α ≃ β) (d : SignedDart α) :
    Corners.start (SignedDart.mapEquiv e d) = Prod.map e id (Corners.start d) := by
  cases d <;> rfl

/-- Corner classes of a one-face presentation can be counted on the typed word. -/
theorem natCard_quot_ofOneFaceWord {Edge : Type} [Fintype Edge] (word : List (SignedDart Edge)) :
    Nat.card (Quot (Corners.Rel (ofOneFaceWord word).faces)) =
      Nat.card (Quot (Corners.Rel [word])) := by
  symm
  let e := Fintype.equivFin Edge
  have hfaces : (ofOneFaceWord word).faces = [word.map (SignedDart.mapEquiv e)] := rfl
  refine natCard_quot_eq_of_maps (Prod.map e id) (Prod.map e.symm id) ?_ ?_ ?_ ?_
  · rintro x y ⟨w, hw, q, hq, rfl, rfl⟩
    rw [List.mem_singleton] at hw
    subst hw
    apply Relation.EqvGen.rel
    refine ⟨_, hfaces ▸ List.mem_singleton_self _,
      Prod.map (SignedDart.mapEquiv e) (SignedDart.mapEquiv e) q, ?_, ?_, ?_⟩
    · rw [Corners.pairs_map]
      exact List.mem_map_of_mem hq
    · simp [finish_mapEquiv]
    · simp [start_mapEquiv]
  · rintro u v ⟨w, hw, q, hq, rfl, rfl⟩
    rw [hfaces, List.mem_singleton] at hw
    subst hw
    rw [Corners.pairs_map, List.mem_map] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    apply Relation.EqvGen.rel
    refine ⟨word, List.mem_singleton_self _, q', hq', ?_, ?_⟩
    · simp only [Prod.map_fst, finish_mapEquiv]
      obtain ⟨a, b⟩ := Corners.finish q'.1
      simp
    · simp only [Prod.map_snd, start_mapEquiv]
      obtain ⟨a, b⟩ := Corners.start q'.2
      simp
  · intro x
    obtain ⟨a, b⟩ := x
    simp only [Prod.map, Equiv.symm_apply_apply, id]
    exact Relation.EqvGen.refl _
  · intro u
    obtain ⟨a, b⟩ := u
    simp only [Prod.map, Equiv.apply_symm_apply, id]
    exact Relation.EqvGen.refl _

theorem orientableBoundaryWord_zero (p : ℕ) :
    orientableBoundaryWord p 0 = (List.finRange p).flatMap (orientableHandleBlock (n := 0)) := by
  simp [orientableBoundaryWord, List.ofFn_eq_map, List.flatMap]

theorem orientableHandleBlock_ne_nil {p : ℕ} (i : Fin p) :
    orientableHandleBlock (n := 0) i ≠ [] := by
  simp [orientableHandleBlock]

/-- All ends of the canonical orientable word are glued to one vertex. -/
theorem eqvGen_orientable_word {p : ℕ} (hp : 1 ≤ p) (x : OrientableEdge p 0 × Bool) :
    Relation.EqvGen (Corners.Rel [orientableBoundaryWord p 0]) x
      (OrientableEdge.a ⟨0, hp⟩, false) := by
  set R := Corners.Rel [orientableBoundaryWord p 0]
  have corner : ∀ q ∈ Corners.pairs (orientableBoundaryWord p 0),
      R (Corners.finish q.1) (Corners.start q.2) := fun q hq =>
    ⟨_, List.mem_singleton_self _, q, hq, rfl, rfl⟩
  have inner : ∀ (i : Fin p) (q : SignedDart (OrientableEdge p 0) × SignedDart (OrientableEdge p 0)),
      q ∈ Corners.lin (orientableHandleBlock (n := 0) i) →
        R (Corners.finish q.1) (Corners.start q.2) := by
    intro i q hq
    apply corner
    rw [orientableBoundaryWord_zero, Corners.mem_pairs_flatMap orientableHandleBlock_ne_nil]
    exact Or.inl ⟨i, List.mem_finRange i, hq⟩
  -- the four ends of one handle are glued together
  have block : ∀ i : Fin p,
      Relation.EqvGen R (OrientableEdge.a i, true) (OrientableEdge.a i, false) ∧
        Relation.EqvGen R (OrientableEdge.b i, false) (OrientableEdge.a i, false) ∧
        Relation.EqvGen R (OrientableEdge.b i, true) (OrientableEdge.a i, false) := by
    intro i
    have h1 := inner i (.pos (.a i), .pos (.b i)) (by simp [Corners.lin, orientableHandleBlock])
    have h2 := inner i (.pos (.b i), .neg (.a i)) (by simp [Corners.lin, orientableHandleBlock])
    have h3 := inner i (.neg (.a i), .neg (.b i)) (by simp [Corners.lin, orientableHandleBlock])
    simp only [Corners.finish, Corners.start] at h1 h2 h3
    -- h1 : (a, true) ~ (b, false); h2 : (b, true) ~ (a, true); h3 : (a, false) ~ (b, true)
    have e3 := Relation.EqvGen.rel _ _ h3
    have e2 := Relation.EqvGen.rel _ _ h2
    have e1 := Relation.EqvGen.rel _ _ h1
    have bt : Relation.EqvGen R (OrientableEdge.b i, true) (OrientableEdge.a i, false) :=
      Relation.EqvGen.symm _ _ e3
    have at' : Relation.EqvGen R (OrientableEdge.a i, true) (OrientableEdge.a i, false) :=
      Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ e2) bt
    have bf : Relation.EqvGen R (OrientableEdge.b i, false) (OrientableEdge.a i, false) :=
      Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ e1) at'
    exact ⟨at', bf, bt⟩
  -- consecutive handles are glued through the end of `bᵢ`
  have junction : ∀ (k : ℕ) (hk : k + 1 < p),
      R (OrientableEdge.b ⟨k, by omega⟩, false) (OrientableEdge.a ⟨k + 1, hk⟩, false) := by
    intro k hk
    have hpair : ((⟨k, by omega⟩ : Fin p), (⟨k + 1, hk⟩ : Fin p)) ∈
        Corners.pairs (List.finRange p) := by
      rw [Corners.mem_pairs]
      refine ⟨k, by simp; omega, ?_⟩
      simp [Nat.mod_eq_of_lt hk]
    have h := corner (.neg (.b ⟨k, by omega⟩), .pos (.a ⟨k + 1, hk⟩)) (by
      rw [orientableBoundaryWord_zero, Corners.mem_pairs_flatMap orientableHandleBlock_ne_nil]
      exact Or.inr ⟨_, hpair, by simp [orientableHandleBlock]⟩)
    simpa [Corners.finish, Corners.start] using h
  -- every `aₖ` is glued to `a₀`
  have chain : ∀ (k : ℕ) (hk : k < p),
      Relation.EqvGen R (OrientableEdge.a ⟨k, hk⟩, false) (OrientableEdge.a ⟨0, hp⟩, false) := by
    intro k
    induction k with
    | zero => intro hk; exact Relation.EqvGen.refl _
    | succ k ih =>
      intro hk
      have hj := junction k hk
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hj))
        (Relation.EqvGen.trans _ _ _ (block ⟨k, by omega⟩).2.1 (ih (by omega)))
  obtain ⟨y, s⟩ := x
  cases y with
  | a i =>
    cases s
    · exact chain i.val i.isLt
    · exact Relation.EqvGen.trans _ _ _ (block i).1 (chain i.val i.isLt)
  | b i =>
    cases s
    · exact Relation.EqvGen.trans _ _ _ (block i).2.1 (chain i.val i.isLt)
    · exact Relation.EqvGen.trans _ _ _ (block i).2.2 (chain i.val i.isLt)
  | c i => exact i.elim0
  | h i => exact i.elim0

/-- The edge names of the closed orientable normal form are `aᵢ` and `bᵢ`. -/
def orientableEdgeEquiv (p : ℕ) : OrientableEdge p 0 ≃ Fin p ⊕ Fin p where
  toFun
    | .a i => Sum.inl i
    | .b i => Sum.inr i
    | .c i => i.elim0
    | .h i => i.elim0
  invFun
    | Sum.inl i => .a i
    | Sum.inr i => .b i
  left_inv x := by
    cases x with
    | a i => rfl
    | b i => rfl
    | c i => exact i.elim0
    | h i => exact i.elim0
  right_inv x := by
    cases x <;> rfl

theorem eulerChar_canonical_orientable {p : ℕ} (hp : 1 ≤ p) :
    eulerChar (canonicalPresentation (.orientable p 0)) = 2 - 2 * p := by
  have hcard : Fintype.card (OrientableEdge p 0) = 2 * p := by
    rw [Fintype.card_congr (orientableEdgeEquiv p), Fintype.card_sum, Fintype.card_fin]
    ring
  have hV : Nat.card (Quot (Corners.Rel (canonicalPresentation (.orientable p 0)).faces)) = 1 := by
    rw [canonicalPresentation_orientable, natCard_quot_ofOneFaceWord, Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun q₁ q₂ => ?_⟩, ⟨Quot.mk _ (OrientableEdge.a ⟨0, hp⟩, false)⟩⟩
    induction q₁ using Quot.ind with
    | mk x =>
      induction q₂ using Quot.ind with
      | mk y =>
        exact (Quot.eqvGen_sound (eqvGen_orientable_word hp x)).trans
          (Quot.eqvGen_sound (eqvGen_orientable_word hp y)).symm
  have hE : (canonicalPresentation (.orientable p 0)).edgeCount = 2 * p := by
    rw [canonicalPresentation_orientable]
    exact hcard
  have hF : (canonicalPresentation (.orientable p 0)).faces.length = 1 := by
    rw [canonicalPresentation_orientable]
    exact ofOneFaceWord_faces_length _
  have hempty : emptyFaceCount (canonicalPresentation (.orientable p 0)) = 0 := by
    rw [canonicalPresentation_orientable, emptyFaceCount, Nat.card_eq_zero]
    left
    refine ⟨fun ⟨f, hf⟩ => ?_⟩
    have hlen := congrArg List.length (ofOneFaceWord_boundary (orientableBoundaryWord p 0) f)
    rw [hf, List.length_nil, List.length_map, orientableBoundaryWord_length] at hlen
    omega
  unfold eulerChar vertexCount
  rw [hV, hempty, hF, hE]
  push_cast
  ring

theorem eulerChar_twoMonogonSphere : eulerChar FiniteCyclicPresentation.twoMonogonSphere = 2 := by
  have hV : Nat.card (Quot (Corners.Rel FiniteCyclicPresentation.twoMonogonSphere.faces)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    have key : ∀ x : Fin 1 × Bool,
        Relation.EqvGen (Corners.Rel FiniteCyclicPresentation.twoMonogonSphere.faces) x (0, false) := by
      have h : Corners.Rel FiniteCyclicPresentation.twoMonogonSphere.faces (0, true) (0, false) :=
        ⟨[.pos 0], by simp, (.pos 0, .pos 0), by simp [Corners.pairs], rfl, rfl⟩
      rintro ⟨i, b⟩
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      cases b
      · exact Relation.EqvGen.refl _
      · exact Relation.EqvGen.rel _ _ h
    refine ⟨⟨fun q₁ q₂ => ?_⟩, ⟨Quot.mk _ (0, false)⟩⟩
    induction q₁ using Quot.ind with
    | mk x =>
      induction q₂ using Quot.ind with
      | mk y => exact (Quot.eqvGen_sound (key x)).trans (Quot.eqvGen_sound (key y)).symm
  have hempty : emptyFaceCount FiniteCyclicPresentation.twoMonogonSphere = 0 := by
    rw [emptyFaceCount, Nat.card_eq_zero]
    left
    exact ⟨fun ⟨f, hf⟩ => FiniteCyclicPresentation.twoMonogonSphere_boundary_nonempty f hf⟩
  unfold eulerChar vertexCount
  rw [hV, hempty]
  rfl

end Canonical

end R4Embedding
