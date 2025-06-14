import Vizing.new.Graph
import Mathlib.Tactic
import Mathlib.Data.List.Lemmas
import Mathlib.Data.Finset.Card

set_option linter.dupNamespace false

namespace EdgeColoring
open Graph

/-
Implementation of a basic edge-coloring library,
where `EdgeColoring c` represents a c-edge-coloring of a graph on [n] vertices.
-/

variable (c : Nat) (n : Nat) (G : Graph n)
abbrev Color := Option (Fin c)

def coloringSizeAx (C : Array (Array (Color c))) :=
  C.size = n ∧ ∀ x ∈ C, x.size = n

abbrev Mat := {C : Array (Array (Color c)) // coloringSizeAx c n C}

def set_set (M : Mat c n) (a : Color c)
  (i j : Fin n) : Mat c n :=
  have ⟨M, ⟨h1, h2⟩⟩ := M
  let M' := M.set i (M[i].set j a (by simp_all)) (by simp_all)
  have h : coloringSizeAx c n M' := by
    simp_all [coloringSizeAx, M']
    intro x h
    rcases (Array.mem_or_eq_of_mem_set h) with (this | this)
    · simp_all only [M']
    · rw [this]
      simp_all [Array.size_set]
  ⟨M', h⟩

theorem set_set_spec (M : Mat c n) (a : Color c) (i j : Fin n) :
  have ⟨N, ⟨hn1, hn2⟩⟩ := set_set c n M a i j
  have ⟨M, ⟨hm1, hm2⟩⟩ := M
  ∀ u v : Fin n,
    (M[u]'(by simp_all))[v]'(by simp_all) = (N[u]'(by simp_all))[v]'(by simp_all) ∨
    (N[u]'(by simp_all))[v]'(by simp_all) = a ∧ i = u ∧ j = v := by
    simp_all; repeat split
    rename_i _ N hn1 hn2 _ M hm1 hm2 N_def
    intro u v
    unfold set_set at N_def; simp at N_def; subst N_def
    by_cases h : i = u ∧ j = v
    · right
      constructor
      · rcases h with ⟨hl, hr⟩
        rw [← hl, ← hr]
        simp_all
      · exact h
    · left
      by_cases h' : i = u
      · simp_all
        exact Eq.symm (@Array.getElem_set_ne _ M[u] j
        (by simp_all) a v (by simp_all) (by exact Fin.val_ne_of_ne h))
      · have := @Array.getElem_set_ne _ M i (by simp_all)
          (M[i].set j a (by simp_all)) u (by simp_all) (by exact Fin.val_ne_of_ne h')
        simp_all

def coloringRepresentsEdgesAx (C : Mat c n) (G : Graph n) :=
  have aux1 : ∀ e : Edge n, e.1 < C.val.size := by
    intro e
    linarith [(e.1).isLt, C.prop.left]
  have aux2 : ∀ e : Edge n, e.2 < (C.val[e.1]'(aux1 e)).size := by
    intro e
    have h1 := C.prop.right (C.val[e.1]'(aux1 e))
    have h2 := (e.2).isLt
    simp at h1
    exact Nat.lt_of_lt_of_eq h2 (Eq.symm h1)
  let E := toEdgeSet n G
  ∀ e : Edge n, ((C.val[e.1]'(aux1 e))[e.2]'(aux2 e)).isSome → present n G e

def coloringValidAx (C : Mat c n) :=
  have aux : ∀ v : Vertex n, v < C.val.size := by
    intro v
    linarith [v.isLt, C.prop.left]
  ∀ v : Vertex n, (List.filterMap id (C.val[v]'(aux v)).toList).Nodup

def coloringSymmAx (C : Mat c n) :=
  have ⟨C, ⟨h1, h2⟩⟩ := C
  ∀ u v : Fin n, (C[u]'(by simp_all))[v]'(by simp_all) = (C[v]'(by simp_all))[u]'(by simp_all)

abbrev EdgeColoring := {C : Mat c n // coloringRepresentsEdgesAx c n C G ∧ coloringValidAx c n C ∧ coloringSymmAx c n C}

variable (C : EdgeColoring c n G)
@[simp]
theorem edgesInRange (e : Edge n) :
  e.1 < C.val.val.size ∧
  e.2 < (C.val.val[e.1]'(by simp_all only [Fin.is_lt, C.val.prop.left])).size := by
    have ⟨⟨C, ⟨h1, h2⟩⟩, h3⟩ := C
    constructor
    all_goals simp_all

theorem verticesInRange (v : Vertex n) :
  v < C.val.val.size := by
  have ⟨⟨C, ⟨h1, _⟩⟩, _⟩ := C
  simp_all

def color (e : Edge n) : Color c :=
  have ⟨aux1, aux2⟩ := edgesInRange c n G C e
  C.val.val[e.1][e.2]

def coloredNbors (v : Vertex n) : Nbors n :=
  have aux1 := verticesInRange c n G C v
  have ⟨⟨C, ⟨h1, h2⟩⟩, ⟨h3, h4⟩⟩ := C
  have := G.prop.right
  have aux2 : C[v].size = n := by
    simp_all
  have aux3 : ∀ x : Vertex n, x < C[v].size := by
    simp_all
  let N := (List.finRange n).filter (fun x => (C[v][x]'(aux3 x)).isSome)
  have ax1 : nborsSizeAx n N := by
    have h4: v ∉ N := by
      specialize h3 (v, v)
      simp_all [N]
      contrapose! h3
      constructor
      · exact Option.isSome_iff_ne_none.mpr h3
      · have := G.prop.right v
        simp_all [present, nbhd]
    have h5 : N.length ≤ (List.finRange n).length := by
      apply List.length_filter_le
    rcases lt_or_eq_of_le h5 with (h5 | h5)
    · simp_all; assumption
    · unfold N at h4 h5
      apply List.length_filter_eq_length_iff.mp at h5
      specialize h5 v (by exact List.mem_finRange v)
      simp_all
  have ax2 : nborsRepeatsAx n N := by
    apply List.Nodup.filter
    exact List.nodup_finRange n
  ⟨N, ⟨ax1, ax2⟩⟩

def incidentColorsOn (v : Vertex n) :=
  have := verticesInRange c n G C v
  ((C.val.val[v]).filterMap id).toList

theorem incident_colors_of_colored_nbors (v : Vertex n) :
  incidentColorsOn c n G C v =
  (coloredNbors c n G C v).val.filterMap (fun x => color c n G C (v, x)) := by
  unfold incidentColorsOn coloredNbors color
  simp_all [List.filterMap_filter]
  split; rename_i _ _ C h1 h2 _ _
  simp_all [List.filterMap_filter, Option.isSome_iff_ne_none]
  have : C[v].toList = List.map (fun x ↦ C[v][x]'(by simp_all)) (List.finRange n) := by
    ext1 i
    simp [Option.map]; split
    all_goals rename_i _ j hj
    · apply Array.getElem?_eq_some_iff.mpr
      rcases (List.getElem?_eq_some_iff.mp hj) with ⟨k, _⟩
      have : (List.finRange n).length = n := by exact List.length_finRange
      rw [List.length_finRange] at k
      simp_all; congr
      rename_i h; rw [← h]
    · apply Array.getElem?_eq_none_iff.mpr
      have := List.getElem?_eq_none_iff.mp hj
      rw [List.length_finRange] at this
      specialize h2 C[v] (by exact Array.mem_of_getElem rfl)
      simp_all
  simp_all; congr
  funext x
  split_ifs
  · assumption
  · split; rfl

theorem colored_nbors_subset_nbors (v : Vertex n) :
  (coloredNbors c n G C v).val ⊆ (nbhd n G v).val := by
  simp [coloredNbors]
  split
  case _ _ C _ _ h _ =>
  intro x h'
  simp_all
  specialize h (v, x) h'
  simp [present] at h
  exact h.right

theorem nodup_subset_eq_length_le {α : Type} [DecidableEq α] (L M : List α)
  (hl : L.Nodup) (hm : M.Nodup) (hsubset : L ⊆ M) : L.length ≤ M.length := by
  rw [← List.toFinset_card_of_nodup hl, ← List.toFinset_card_of_nodup hm]
  apply Finset.card_le_card
  repeat any_goals rw [← List.toFinset_eq]
  repeat assumption

theorem nodup_exists_mem_notMem_of_len_lt {α : Type} [DecidableEq α] (L M : List α)
  (hl : L.Nodup) (hm : M.Nodup) (hlen : L.length < M.length) :
  ∃ x ∈ M, x ∉ L := by
  rw [← List.toFinset_card_of_nodup hl, ← List.toFinset_card_of_nodup hm] at hlen
  apply Finset.exists_mem_notMem_of_card_lt_card at hlen
  simp_all

theorem colored_nbhd_size_le (v : Vertex n) :
  (coloredNbors c n G C v).val.length ≤ degree n G v := by
  let N := coloredNbors c n G C v
  let X := nbhd n G v
  simp [degree]
  apply nodup_subset_eq_length_le
  · exact N.prop.right
  · exact X.prop.right
  · exact colored_nbors_subset_nbors c n G C v

def default : EdgeColoring c n G :=
  have ⟨⟨X, h1⟩, ⟨h2, h3⟩⟩ := G
  let C : Array (Array (Color c)) :=
    Array.replicate X.size (Array.replicate X.size none)
  have ax1 : coloringSizeAx c n C := by
    unfold coloringSizeAx C
    simp_all
    constructor
    any_goals intro _
    all_goals exact h1
  have ax2 : coloringRepresentsEdgesAx c n ⟨C, ax1⟩ ⟨⟨X, h1⟩, ⟨h2, h3⟩⟩ := by
    simp [coloringRepresentsEdgesAx]
    intro a b h
    simp [C] at h
  have ax3 : coloringValidAx c n ⟨C, ax1⟩ := by
    simp [coloringValidAx, C]
  have ax4 : coloringSymmAx c n ⟨C, ax1⟩ := by
    simp [coloringSymmAx, C]
    split; simp_all
    rename_i _ _ _ _ h; subst h
    simp
  ⟨⟨C, ax1⟩, ⟨ax2, ax3, ax4⟩⟩

/-

def coloringValidAx (C : Mat c n) :=
  have aux : ∀ v : Vertex n, v < C.val.size := by
    intro v
    linarith [v.isLt, C.prop.left]
  ∀ v : Vertex n, (List.filterMap id (C.val[v]'(aux v)).toList).Nodup


-/

def edgeColorValid (e : Edge n) (a : Color c) : Prop :=
  have ⟨_, _⟩ := edgesInRange c n G C e
  have ⟨⟨C, ⟨_, _⟩⟩, ⟨_, _⟩⟩ := C
  a ∉ C[e.1] ∧ a ∉ C[e.2]


def setEdgeColor (e : Edge n) (a : Color c)
  (h : present n G e) (h' : edgeColorValid c n G C e a) : EdgeColoring c n G :=
  have ⟨h1, h2⟩ := edgesInRange c n G C e
  have ⟨⟨C, ⟨ax1, ax2⟩⟩, ⟨ax3, ax4⟩⟩ := C
  let C' := C.set e.1 <| C[e.1].set e.2 a
  have aux1 : coloringSizeAx c n C' := by
    unfold coloringSizeAx C' at *
    constructor
    · simp_all only [Fin.getElem_fin, Array.size_set]
    · intro x h
      have := Array.mem_or_eq_of_mem_set h
      rcases this with this | this
      all_goals simp_all only [Fin.getElem_fin, Array.size_set, Array.getElem_mem]
  have aux2 : coloringRepresentsEdgesAx c n ⟨C', aux1⟩ G := by
    unfold coloringRepresentsEdgesAx at *
    simp; simp at ax3
    intro u v h3
    by_cases huv : e.1 = u ∧ e.2 = v
    · rcases huv with ⟨hl, hr⟩
      rw [← hl, ← hr]
      exact h
    apply ax3 u v
    simp [C'] at h3; simp at huv
    by_cases hu : e.1 = u
    · have := @Array.getElem_set_ne _ C[u] e.2 (by simp_all) a v (by simp_all)
      specialize this (by exact Fin.val_ne_of_ne (huv hu))
      simp_all
    · have := @Array.getElem_set_ne _ C e.1 h1 (C[e.1].set e.2 a) u (by simp_all)
      specialize this (by exact Fin.val_ne_of_ne hu)
      simp_all
  have aux3 : coloringValidAx c n ⟨C', aux1⟩ := by
    simp [coloringValidAx, C']
    sorry
  ⟨⟨C', aux1⟩, ⟨aux2, aux3⟩⟩

def allColors : List (Fin c) := List.finRange c

def freeColorsOn (v : Vertex n) :=
  (allColors c).filter (fun x => x ∉ incidentColorsOn c n G C v)

theorem existsFreeColor (h : ↑(maxDegree n G) < c) :
  ∀ v : Vertex n, (freeColorsOn c n G C v) ≠ [] := by
  intro v
  simp [freeColorsOn]
  apply nodup_exists_mem_notMem_of_len_lt
  simp [incidentColorsOn]
  · exact (C.prop.right.left) v
  · simp [allColors]
    exact List.nodup_finRange c
  · simp [incident_colors_of_colored_nbors, allColors, List.length_finRange]
    have hle : (coloredNbors c n G C v).val.length < c := by
      have h1 := colored_nbhd_size_le c n G C v
      have h2 := maxDegree_spec n G v
      exact lt_of_le_of_lt (le_trans h1 h2) h
    have hlt := List.length_filterMap_le
      (fun x ↦ color c n G C (v, x)) ↑(coloredNbors c n G C v)
    exact Nat.lt_of_le_of_lt hlt hle


/-

No self edges


-/

#exit

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
