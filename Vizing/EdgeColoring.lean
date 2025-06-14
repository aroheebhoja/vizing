import Vizing.Graph
import Mathlib.Tactic
set_option linter.dupNamespace false

namespace EdgeColoring
open Graph

/-
Implementation of a basic edge-coloring library,
where `EdgeColoring c` represents a c-edge-coloring of a graph on [n] vertices.
-/

variable (c : Nat) (n : Nat) (G : Graph n)
  (nonempty : 0 < c)
  (graphsize : G.size = n)
  (edgeSet_symm : ∀ u v : Vertex n, (u, v) ∈ (edgeSet n G graphsize) ↔ v ∈ nbors n G graphsize u ∧ u ∈ nbors n G graphsize v)
  (nbors_symm : ∀ u v : Vertex n, v ∈ nbors n G graphsize u ↔ u ∈ nbors n G graphsize v)

-- We choose 0 as the default value, to represent an uncolored edge

abbrev Color := Fin (c + 1)
abbrev EdgeColoring := Array (Array (Color c))

variable
  (C : EdgeColoring c)
  (edgecoloring1 : C.size = n ∧ ∀ x ∈ C, x.size = n)

include edgecoloring1

theorem cx' (v : Vertex n) : v < C.size := by
  rw [(edgecoloring1).left]
  exact v.isLt

-- Accessing the color of an edge is always in bound
theorem cx (e : Edge n) : e.1 < C.size ∧
  e.2 < (C[e.1]'(cx' c n C edgecoloring1 e.1)).size := by
  constructor
  · exact cx' c n C edgecoloring1 e.1
  · rw [(edgecoloring1).right]
    · exact e.2.isLt
    · exact Array.mem_of_getElem rfl

def color (e : Edge n) :=
  have := cx c n C edgecoloring1 e
  C[e.1][e.2]

def coloring_valid (C : EdgeColoring c) (h : C.size = n ∧ ∀ x ∈ C, x.size = n) :=
  ∀ v : Vertex n, ((C[v]'(cx' c n C h v)).filter (fun c => c ≠ 0)).size ≤ degree n G graphsize v

def default : EdgeColoring c :=
  mkArray G.size (mkArray G.size 0)

omit edgecoloring1 in
include graphsize in
theorem default_spec :
  (default c n G).size = n ∧ ∀ x ∈ (default c n G), x.size = n := by
  simp only [default, Array.size_mkArray, Array.mem_mkArray, ne_eq, List.length_eq_zero,
    Array.toList_eq_nil_iff, and_imp, forall_eq_apply_imp_iff]
  constructor
  exact graphsize
  intro h; exact graphsize

omit edgecoloring1 in
theorem default_spec' : coloring_valid c n G graphsize
  (default c n G) (default_spec c n G graphsize) := by
  simp [coloring_valid, default]

def allColors : List (Color c) :=
  let L := List.finRange (c + 1)
  have : 0 < c + 1 := by
    exact Nat.add_pos_left nonempty 1
  L.erase ⟨0, this⟩

variable
  (edgecoloring2 : coloring_valid c n G graphsize C edgecoloring1)
  (edgecoloring3 : ∀ u v, u ∉ nbors n G graphsize v → color c n G C edgecoloring1 (u, v) = 0)

def setEdgeColor (e : Edge n) (a : Color c) : EdgeColoring c :=
  let e' := (e.2, e.1)
  have := cx c n C edgecoloring1 e
  let C' := C.set e.1 <| C[e.1].set e.2 a
  have h1 : C'.size = n := by
    simp only [Fin.getElem_fin, Array.size_set, C']; exact edgecoloring1.left
  have h2 : ∀ x ∈ C', x.size = n := by
    simp only [Fin.getElem_fin, C']
    intro x hx
    have := Array.mem_or_eq_of_mem_set hx
    rcases this with l | r
    exact edgecoloring1.right x l
    simp only [r, Array.size_set, Array.getElem_mem, edgecoloring1, C']
  have := cx c n C' ⟨h1, h2⟩ e'
  C'.set e'.1 <| C'[e'.1].set e'.2 a

example (x : α) (A : Array α) (i : Nat) (h : i < A.size) :
  x = A[i] → x ∈ A := by
  exact fun a ↦ Array.mem_of_getElem (id (Eq.symm a))

theorem setEdgeColor_spec (e : Edge n) (a : Color c) :
  (setEdgeColor c n G C edgecoloring1 e a).size = n ∧
  ∀ x ∈ (setEdgeColor c n G C edgecoloring1 e a), x.size = n := by
  simp only [setEdgeColor, Fin.getElem_fin, Array.size_set]
  constructor
  exact edgecoloring1.left
  intro x hx
  have := Array.mem_or_eq_of_mem_set hx
  rcases this with this | this
  · have := Array.mem_or_eq_of_mem_set this
    rcases this with l | r
    exact edgecoloring1.right x l
    simp only [r, Array.size_set, Array.getElem_mem, edgecoloring1]
  · have aux := cx c n C edgecoloring1 e
    have h1 : ((Array.set C (↑e.fst) (C[↑e.fst].set (↑e.snd) a))).size = n := by
      simp only [Fin.getElem_fin, Array.size_set, edgecoloring1]
    have h2 : ∀ x ∈ ((Array.set C (↑e.fst) (C[↑e.fst].set (↑e.snd) a))), x.size = n := by
      intro x hx
      have := Array.mem_or_eq_of_mem_set hx
      rcases this with l | r
      exact edgecoloring1.right x l
      simp [r, Array.size_set, Array.getElem_mem]
      have : C[↑e.fst] ∈ C := by
        exact Array.mem_of_getElem rfl
      exact edgecoloring1.right C[↑e.fst] this
    have h3 : ((Array.set C (↑e.fst) (C[↑e.fst].set (↑e.snd) a)))[↑e.snd].size = n := by
      simp_all only [Fin.is_lt, Fin.getElem_fin, Array.getElem_mem]
    have h4 := Array.size_set ((Array.set C (↑e.fst) (C[↑e.fst].set (↑e.snd) a))[↑e.snd])
    simp only [h3] at h4
    simp_all only [Fin.is_lt, Fin.getElem_fin, Array.size_set, Array.getElem_mem, implies_true]

include edgecoloring3 in
theorem aux (e : Edge n) (a : Color c) (h : e ∈ edgeSet n G graphsize) :
  ∀ u v, u ∉ nbors n G graphsize v → color c n G (setEdgeColor c n G C edgecoloring1 e a)
  (setEdgeColor_spec c n G C edgecoloring1 e a) (u, v) = 0 := by
  intro u v h2
  specialize edgecoloring3 u v h2
  simp [setEdgeColor, color] at *
  let C' := setEdgeColor c n G C edgecoloring1 e a
  have h' := setEdgeColor_spec c n G C edgecoloring1 e a
  have aux := cx' c n C' h'
  have : ∀ v, v ≠ e.1 ∧ v ≠ e.2 → C[v] = C'[v]'(aux v) := by
    intro v h
    simp [C', setEdgeColor]
    repeat rw [Array.getElem_set_ne]
    all_goals apply Fin.val_ne_of_ne; apply Ne.symm
    exact h.left
    exact h.right
  rw [← edgecoloring3]
  have : ∀ f : Edge n, f.1 ≠ e.1 ∧ f.1 ≠ e.2 → color c n G C edgecoloring1 f = color c n G C' h' f := by
    intro f hf
    simp [color, C', setEdgeColor]
    have aux := this f.1 hf
    simp [C', setEdgeColor] at aux
    simp [aux]
  simp [color, C', setEdgeColor] at this
  specialize this u v
  apply Eq.symm
  apply this
  sorry
  sorry

def setEdgeColor_spec' (e : Edge n) (a : Color c) (h : e ∈ edgeSet n G graphsize) :
  coloring_valid c n G graphsize (setEdgeColor c n G C edgecoloring1 e a)
  (setEdgeColor_spec c n G C edgecoloring1 e a) := by
  let C' := setEdgeColor c n G C edgecoloring1 e a
  have h' := setEdgeColor_spec c n G C edgecoloring1 e a
  have aux := cx' c n C' h'
  have : ∀ v, v ≠ e.1 ∧ v ≠ e.2 → C[v] = C'[v]'(aux v) := by
    intro v h
    simp [C', setEdgeColor]
    repeat rw [Array.getElem_set_ne]
    all_goals apply Fin.val_ne_of_ne; apply Ne.symm
    exact h.left
    exact h.right
  unfold coloring_valid degree at *
  intro v
  by_cases h : v ≠ e.1 ∧ v ≠ e.2
  · specialize this v h
    unfold C' at this
    rw [← this]
    exact edgecoloring2 v
  · by_cases h2 : v = e.1
    dsimp -zeta [setEdgeColor]
    rw [h2]
    repeat rw [Array.getElem_set_self]
    simp only
    sorry
    sorry
    sorry

def getIncidentColors (v : Vertex n) : List (Color c) :=
  (nbors n G graphsize v).map (fun a => color c n G C edgecoloring1 (v, a))

def getNborWithColor? (v : Vertex n) (a : Color c) : Option (Vertex n) :=
  let choices := (nbors n G graphsize v).filter (fun x => color c n G C edgecoloring1 (v, x) = a)
  match choices with
  | [] => none
  | u :: _ => some u

def getFreeColors (v : Vertex n) : List (Color c) :=
  let incident := getIncidentColors c n G graphsize C edgecoloring1 v
  (allColors c nonempty).filter (fun x => x ∉ incident)

def freeOn (a : Color c) (v : Vertex n) :=
  a ∈ getFreeColors c n G nonempty graphsize C edgecoloring1 v

def incidentOn (a : Color c) (v : Vertex n) :=
  a ∈ getIncidentColors c n G graphsize C edgecoloring1 v

include edgecoloring2 in
theorem existsFreeColor (h : maxDegree n G graphsize < c) :
  ∀ v, getFreeColors c n G nonempty graphsize C edgecoloring1 v ≠ [] := by
  intro v hv
  have h1 : C[v].size = n := by
    apply edgecoloring1.right
    exact Array.mem_of_getElem rfl
  simp [*, getFreeColors, getIncidentColors, allColors, color, nbors] at hv
  let X := (List.finRange (c + 1)).erase 0
  let Y := (C[v].filter (fun a => a ≠ 0))
  have h2 : ∀ a ∈ X, a ∈ C[v] := by
    intro a ha
    have := hv a ha
    rcases this with ⟨x, hx1, hx2⟩
    exact Array.mem_of_getElem hx2
  have h3 : ∀ a ∈ X, a ∈ Y := by
    intro a ha
    have aux1 := h2 a ha
    simp only [X, List.finRange, List.ofFn_succ, List.erase_cons_head, List.mem_ofFn,
      Fin.exists_succ_eq, ne_eq] at ha
    simp only [Y, Fin.getElem_fin, ne_eq, decide_not, id_eq, Int.reduceNeg, Array.mem_filter,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    exact ⟨aux1, ha⟩
  have h4 : X.length = c := by
    simp only [X, List.mem_finRange, List.length_erase_of_mem, List.length_finRange,
      add_tsub_cancel_right]
  have h5 : Y.size ≥ c := by
    have aux1 : X ⊆ Y.toList := by
      simp [List.subset_def]
      intro a ha
      exact h3 a ha
    have aux2 : X.Nodup := by
      simp [X, List.finRange, List.Nodup]
      intro i j hij
      exact Fin.ne_of_lt hij
    have aux3 : X.toFinset.card = X.length := by
      have : (List.finRange (c+1)).erase 0 = ((List.finRange (c+1)).erase 0).dedup := by
        exact Eq.symm (List.Nodup.dedup aux2)
      simp [List.toFinset, Multiset.toFinset, X, List.finRange, List.ofFn, this]
    have aux4 : Y.toList.toFinset.card ≤ Y.toList.length := by
      exact List.toFinset_card_le Y.toList
    simp [← h4]
    have aux5 : X.toFinset ⊆ Y.toList.toFinset := by
      simp [Finset.subset_def]
      have : X = X.dedup := by exact Eq.symm (List.Nodup.dedup aux2)
      rw [← this]
      have : Y.toList ⊆ Y.toList.dedup := by exact List.subset_dedup Y.toList
      exact fun _ x ↦ this (aux1 x)
    have aux6 : X.toFinset.card ≤ Y.toList.toFinset.card := by
      exact Finset.card_le_card aux5
    rw [aux3] at aux6
    exact Nat.le_trans aux6 aux4
  specialize edgecoloring2 v
  have := maxDegree_spec n G graphsize v
  have : degree n G graphsize v < c := by linarith
  have : Y.size < c := by
    exact lt_of_le_of_lt edgecoloring2 this
  linarith

end EdgeColoring
