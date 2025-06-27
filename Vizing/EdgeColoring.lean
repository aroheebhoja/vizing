import Vizing.Graph
import Vizing.SetSet
import Vizing.Nbhd

set_option linter.dupNamespace false
set_option push_neg.use_distrib true

namespace EdgeColoring
open Graph
open Aux

/-
Implementation of a basic edge-coloring library,
where `EdgeColoring c` represents a c-edge-coloring of a graph on [n] vertices.
-/

variable {n : Nat} {c : Nat} (G : Graph n) (C : EdgeColoring c G)

/-
Can't be a color we already used!
(we don't need to specify any other edge invariants,
   because we know the edge is present in the graph)
-/

def allColors : List (Color c) := (List.finRange c).map some

def freeColorsOn (v : Vertex n) :=
  (allColors).filter (fun x => x ∉ incidentColorsOn c G C v)

def edgeColorValid (e : Edge n) (a : Color c) : Prop :=
  a.isNone ∨ (a ∈ freeColorsOn G C e.1 ∧ a ∈ freeColorsOn G C e.2)

def edgeColorValidAux (e : Edge n) (a : Color c) : Prop :=
  a.isSome →
  Array.count a
  (C.val[e.1]'(by rw [C.sizeAx1]; exact e.1.isLt)) = 0 ∧
  Array.count a
  (C.val[e.2]'(by rw [C.sizeAx1]; exact e.2.isLt)) = 0

theorem edgeColorValid_spec (e : Edge n) (a : Color c) (h : edgeColorValid G C e a) :
  edgeColorValidAux G C e a := by
  simp [edgeColorValid, freeColorsOn, incidentColorsOn] at h
  rcases h with h | h
  · simp_all [edgeColorValidAux]
  · rcases h with ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
    intro h
    simp [Option.isSome_iff_ne_none.mp h] at h1 h2
    constructor
    all_goals
      apply Array.count_eq_zero_of_not_mem
      assumption

variable
  (e : Edge n) (a : Color c)

def setEdge :=
  let h := set_set_preserves_size n C.val C.sizeAx1 C.sizeAx2 a e.1 e.2
  set_set n (set_set n C.val C.sizeAx1 C.sizeAx2 a e.1 e.2)
    (by exact h.left) (by exact h.right) a e.2 e.1

theorem edge_not_self_loop (hpres : present G e) : e.1 ≠ e.2 := by
  by_contra h
  simp [present, nbhd] at hpres
  simp_rw [← Fin.getElem_fin, h] at hpres
  exact G.noSelfLoopsAx e.2 hpres.left

theorem setEdge_symm (hpres : present G e) :
  setEdge G C e a = setEdge G C (e.2, e.1) a := by
  simp [setEdge]
  apply set_set_comm
  right
  exact edge_not_self_loop G e hpres

theorem setEdge_sizeAx1 : (setEdge G C e a).size = n := by
  have h := set_set_preserves_size n C.val C.sizeAx1 C.sizeAx2 a e.1 e.2
  exact (set_set_preserves_size n (set_set n C.val C.sizeAx1 C.sizeAx2 a e.1 e.2)
    (by exact h.left) (by exact h.right) a e.2 e.1).left

theorem setEdge_sizeAx2 : ∀ i : Vertex n,
  ((setEdge G C e a)[i]'(by
    rw [setEdge_sizeAx1]; exact i.isLt)).size = n := by
  have h := set_set_preserves_size n C.val C.sizeAx1 C.sizeAx2 a e.1 e.2
  exact (set_set_preserves_size n (set_set n C.val C.sizeAx1 C.sizeAx2 a e.1 e.2)
    (by exact h.left) (by exact h.right) a e.2 e.1).right

theorem setEdge_spec1 (hpres : present G e) :
  ((setEdge G C e a)[e.1.val]'(by
    rw [setEdge_sizeAx1]; exact e.1.isLt))[e.2.val]'(by
    rw [← Fin.getElem_fin, setEdge_sizeAx2]; exact e.2.isLt) = a := by
    have hsize := set_set_preserves_size n C.val C.sizeAx1 C.sizeAx2 a e.1 e.2
    have h1 := set_set_spec2 n C.val C.sizeAx1 C.sizeAx2 a e.1 e.2 e.1 e.2 (by tauto)
    have h2 := set_set_spec1 n (set_set n C.val C.sizeAx1 C.sizeAx2 a e.1 e.2)
      hsize.left hsize.right a e.2 e.1 e.1 e.2 (by
      right; exact edge_not_self_loop G e hpres)
    rw [h1] at h2
    exact Eq.symm h2

theorem setEdge_spec2 :
  ((setEdge G C e a)[e.2.val]'(by
    rw [setEdge_sizeAx1]; exact e.2.isLt))[e.1.val]'(by
    rw [← Fin.getElem_fin, setEdge_sizeAx2]; exact e.1.isLt) = a := by
    have hsize := set_set_preserves_size n C.val C.sizeAx1 C.sizeAx2 a e.1 e.2
    have h2 := set_set_spec2 n (set_set n C.val C.sizeAx1 C.sizeAx2 a e.1 e.2)
      hsize.left hsize.right a e.2 e.1 e.2 e.1 (by tauto)
    simp [setEdge]
    exact h2

theorem setEdge_spec3 : ∀ u v : Vertex n,
  (e.1 ≠ u ∨ e.2 ≠ v) ∧ (e.2 ≠ u ∨ e.1 ≠ v) →
  (C.val[u.val]'(by
    rw [C.sizeAx1]; exact u.isLt))[v.val]'(by
    rw [← Fin.getElem_fin, C.sizeAx2]; exact v.isLt) =
    ((setEdge G C e a)[u.val]'(by
    rw [setEdge_sizeAx1]; exact u.isLt))[v.val]'(by
    rw [← Fin.getElem_fin, setEdge_sizeAx2]; exact v.isLt) := by
    intro u v h
    have hsize := set_set_preserves_size n C.val C.sizeAx1 C.sizeAx2 a e.1 e.2
    have h1 := set_set_spec1 n C.val C.sizeAx1 C.sizeAx2 a e.1 e.2 u v (by tauto)
    have h2 := set_set_spec1 n (set_set n C.val C.sizeAx1 C.sizeAx2 a e.1 e.2)
      hsize.left hsize.right a e.2 e.1 u v (by tauto)
    rwa [← h1] at h2

theorem setEdge_spec4 : ∀ u : Vertex n,
  (e.1 ≠ u ∧ e.2 ≠ u) →
  C.val[u.val]'(by
    rw [C.sizeAx1]; exact u.isLt) =
    (setEdge G C e a)[u.val]'(by
    rw [setEdge_sizeAx1]; exact u.isLt) := by
    intro u h
    have hsize := set_set_preserves_size n C.val C.sizeAx1 C.sizeAx2 a e.1 e.2
    have h1 := set_set_spec3 n C.val C.sizeAx1 C.sizeAx2 a e.1 e.2 u (by tauto)
    have h2 := set_set_spec3 n (set_set n C.val C.sizeAx1 C.sizeAx2 a e.1 e.2)
      hsize.left hsize.right a e.2 e.1 u (by tauto)
    rwa [← h1] at h2

theorem setEdge_spec5 (hpres : present G e) :
  ∀ b : Color c,
    Array.count b ((setEdge G C e a)[e.1.val]'(by
    rw [setEdge_sizeAx1]; exact e.1.isLt)) =
    Array.count b (C.val[e.1.val]'(by rw [C.sizeAx1]; exact e.1.isLt)) -
    (if (C.val[e.1.val]'(by rw [C.sizeAx1]; exact e.1.isLt))[e.2.val]'(by
      rw [← Fin.getElem_fin, C.sizeAx2 e.1]; exact e.2.isLt) = b then 1 else 0) +
    (if a = b then 1 else 0) := by
    intro b
    have hsize := set_set_preserves_size n C.val C.sizeAx1 C.sizeAx2 a e.1 e.2
    have h1 := count_set_set n C.val C.sizeAx1 C.sizeAx2 a b e.1 e.2
    have h2 := count_set_set' n (set_set n C.val C.sizeAx1 C.sizeAx2 a e.1 e.2)
      hsize.left hsize.right a b e.2 e.1 (by exact Ne.symm (edge_not_self_loop G e hpres))
    have h3 := set_set_spec2 n C.val C.sizeAx1 C.sizeAx2 a e.1 e.2 e.1 e.2 (by tauto)
    rw [h1] at h2
    simp [setEdge, Fin.getElem_fin] at ⊢ h2
    exact h2

theorem setEdge_representsEdgesAx (hpres : present G e) : ∀ f : Edge n,
    (((setEdge G C e a)[f.1]'(by
    rw [setEdge_sizeAx1]; exact f.1.isLt))[f.2]'(by
    rw [setEdge_sizeAx2]; exact f.2.isLt)).isSome → present G f := by
  have hpres_symm : present G (e.2, e.1) := by
    exact ⟨hpres.right, hpres.left⟩
  intro f hf
  by_cases h : (f = e) ∨ (f = (e.2, e.1))
  · rcases h with h | h
    all_goals rwa [h]
  · simp_rw [Prod.eq_iff_fst_eq_snd_eq] at h
    push_neg at h
    have aux := setEdge_spec3 G C e a f.1 f.2 (by tauto)
    simp only [Fin.getElem_fin, ← aux] at hf
    exact C.representsEdgesAx f hf

theorem setEdge_validAx (hpres : present G e)
  (hval : edgeColorValid G C e a) :
  ∀ u v : Vertex n,
    (((setEdge G C e a)[u]'(by
      rw [setEdge_sizeAx1]; exact u.isLt))[v]'(by
      rw [setEdge_sizeAx2]; exact v.isLt)).isSome →
    Array.count (((setEdge G C e a)[u]'(by
      rw [setEdge_sizeAx1]; exact u.isLt))[v]'(by
      rw [setEdge_sizeAx2]; exact v.isLt))
      ((setEdge G C e a)[u]'(by
      rw [setEdge_sizeAx1]; exact u.isLt))
      = 1 := by
  have hvalid := edgeColorValid_spec G C e a hval
  intro u v huv
  have := edge_not_self_loop G e hpres
  by_cases h : e.1 ≠ u ∧ e.2 ≠ u
  · have h1 := setEdge_spec3 G C e a u v (by tauto)
    have h2 := setEdge_spec4 G C e a u h
    simp_rw [Fin.getElem_fin, ← h1, ← h2] at ⊢ huv
    exact C.validAx u v huv
  · push_neg at h
    have spec1 := setEdge_spec1 G C e a hpres
    have spec2 := setEdge_spec2 G C e a
    clear hval
    wlog hu : e.1 = u generalizing e
    specialize this (e.2, e.1)
    have symm := setEdge_symm G C (e.2, e.1) a (And.comm.mp hpres)
    simp at symm
    simp [symm] at this
    apply this
    · exact And.comm.mp (hpres)
    · simp [edgeColorValid] at hvalid ⊢
      intro h
      exact And.comm.mp (hvalid h)
    any_goals simp_all
    (expose_names; exact fun a ↦ hu_1 (id (Eq.symm a)))
    simp_rw [← hu] at *
    by_cases hv : e.2 = v
    · rw [← hv] at ⊢ huv
      simp_rw [spec1] at ⊢ huv
      simp_rw [setEdge_spec5 G C e a hpres a, ← Fin.getElem_fin,
      (hvalid huv).left]
      simp only [Fin.getElem_fin, zero_tsub, ↓reduceIte, zero_add]
    · have aux1 := setEdge_spec3 G C e a e.1 v (by tauto)
      have aux2 := setEdge_spec5 G C e a hpres ((C.val[e.1]'(by
        rw [C.sizeAx1]; exact e.1.isLt))[v]'(by
        rw [C.sizeAx2]; exact v.isLt))
      simp_rw [← aux1] at huv
      have aux3 := C.validAx e.1 v huv
      simp_rw [Fin.getElem_fin] at *
      simp_rw [← aux1, aux2]
      rw [aux3]
      split_ifs with h1 h2
      any_goals ring_nf
      · have aux4 := one_lt_count (C.val[e.1]'(by
          rw [C.sizeAx1]; exact e.1.isLt))
          ⟨v, by simp_rw [C.sizeAx2]; exact v.isLt⟩
          ⟨e.2, by simp_rw [C.sizeAx2]; exact e.2.isLt⟩
          (by simp; exact Fin.val_ne_of_ne fun a ↦ hv (Eq.symm a))
          (by exact beq_iff_eq.mpr (Eq.symm h1))
        simp_rw [Fin.getElem_fin] at aux4
        apply ne_of_gt at aux4
        simp_all
      · rename_i h2
        rw [← h2] at aux3 huv
        obtain ⟨hl, _⟩ := hvalid huv
        apply Array.not_mem_of_count_eq_zero at hl
        rw [h2] at hl
        contrapose! hl
        simp

theorem setEdge_symmAx (hpres : present G e) : ∀ u v : Vertex n,
    (((setEdge G C e a)[u]'(by
      rw [setEdge_sizeAx1]; exact u.isLt))[v]'(by
      rw [setEdge_sizeAx2]; exact v.isLt)) =
    (((setEdge G C e a)[v]'(by
      rw [setEdge_sizeAx1]; exact v.isLt))[u]'(by
      rw [setEdge_sizeAx2]; exact u.isLt)) := by
  intro u v
  by_cases h : (e.1 ≠ u ∨ e.2 ≠ v) ∧ (e.2 ≠ u ∨ e.1 ≠ v)
  · have h1 := setEdge_spec3 G C e a u v h
    have h2 := setEdge_spec3 G C e a v u (by tauto)
    simp_rw [Fin.getElem_fin, ← h1, ← h2]
    exact C.symmAx u v
  · push_neg at h
    rcases h with (⟨hl, hr⟩ | ⟨hl, hr⟩)
    all_goals
    have h1 := setEdge_spec1 G C e a hpres
    have h2 := setEdge_spec2 G C e a
    simp_rw [← hl, ← hr, Fin.getElem_fin, h1, h2]

def setEdgeColor (e : Edge n) (a : Color c)
  (hpres : present G e) (hvalid : edgeColorValid G C e a) :
  EdgeColoring c G where
  val := setEdge G C e a
  sizeAx1 := setEdge_sizeAx1 G C e a
  sizeAx2 := setEdge_sizeAx2 G C e a
  representsEdgesAx := setEdge_representsEdgesAx G C e a hpres
  validAx := setEdge_validAx G C e a hpres hvalid
  symmAx := setEdge_symmAx G C e a hpres

theorem incidentColors_invariant (e : Edge n) (a : Color c)
  (hpres : present G e) (hvalid : edgeColorValid G C e a) :
  ∀ v : Vertex n, v ≠ e.1 ∧ v ≠ e.2 → incidentColorsOn c G C v =
    incidentColorsOn c G (setEdgeColor G C e a hpres hvalid) v := by
  intro v _
  simp [incidentColorsOn, setEdgeColor]
  have := setEdge_spec4 G C e a v (by tauto)
  rw [this]

theorem freeColors_invariant (e : Edge n) (a : Color c)
  (hpres : present G e) (hvalid : edgeColorValid G C e a) :
  ∀ v : Vertex n, v ≠ e.1 ∧ v ≠ e.2 → freeColorsOn G C v =
    freeColorsOn G (setEdgeColor G C e a hpres hvalid) v := by
  intro v h
  simp only [freeColorsOn]
  rw [incidentColors_invariant G C e a hpres hvalid v h]

theorem color_invariant (e : Edge n) (a : Color c)
  (hpres : present G e) (hvalid : edgeColorValid G C e a) :
  ∀ f : Edge n, f ≠ e ∧ f ≠ (e.2, e.1) →
  color c G C f = color c G (setEdgeColor G C e a hpres hvalid) f := by
  intro f h
  simp [setEdgeColor]
  apply setEdge_spec3
  simp_rw [ne_eq, Prod.eq_iff_fst_eq_snd_eq] at h
  tauto

theorem existsFreeColor (h : ↑(maxDegree G) < c) :
  ∀ v : Vertex n, (freeColorsOn G C v) ≠ [] := by
  intro v
  simp [freeColorsOn]
  apply exists_mem_notMem_of_nodup_of_len_lt
  · apply List.nodup_iff_count_le_one.mpr
    have hvalid := C.validAx v
    simp_all [incidentColorsOn]
    intro a
    by_cases ha : Option.isSome a
    have := @List.count_filter (Color c) instBEqOfDecidableEq _ _ _
      (C.val[v]'(by rw [C.sizeAx1]; exact v.isLt)).toList ha
    rw [← Fin.getElem_fin, this]
    simp [Array.count_toList, Array.count_eq_countP,
      Bool.beq_eq_decide_eq] at hvalid ⊢
    · by_cases h : a ∈ C.val[v]'(by rw [C.sizeAx1]; exact v.isLt)
      · apply le_iff_lt_or_eq.mpr
        right
        rcases (Array.getElem_of_mem h) with ⟨i, hi1, hi2⟩
        subst hi2
        exact hvalid ⟨i, (by rw [C.sizeAx2] at hi1; exact hi1)⟩ ha
      · apply Nat.le_one_iff_eq_zero_or_eq_one.mpr
        left
        apply Array.count_eq_zero_of_not_mem at h
        simp only [Fin.getElem_fin, Array.count_eq_countP,
        Bool.beq_eq_decide_eq] at h
        exact h
    · simp_all
      apply Nat.le_one_iff_eq_zero_or_eq_one.mpr
      left
      simp [List.count_eq_zero.mpr]
  · simp [allColors]
    apply (List.nodup_map_iff _).mpr
    · exact List.nodup_finRange c
    · exact Option.some_injective (Fin c)
  · simp [incident_colors_of_colored_nbors, allColors, List.length_finRange]
    have hlt : (coloredNbors c G C v).val.length < c := by
      have h1 := colored_nbhd_size_le c G C v
      have h2 := maxDegree_spec G v
      exact lt_of_le_of_lt (le_trans h1 h2) h
    have hle : (List.filter Option.isSome
      (List.map (fun x ↦ color c G C (v, x))
      (coloredNbors c G C v).val)).length ≤
      (coloredNbors c G C v).val.length := by
      have := List.length_filter_le Option.isSome
            (List.map (fun x ↦ color c G C (v, x)) (coloredNbors c G C v).val)
      rw [List.length_map] at this
      exact this
    exact Nat.lt_of_le_of_lt hle hlt

theorem newColor_not_eq_oldColor (e : Edge n) (a : Color c)
  (hvalid : edgeColorValid G C e a) (hcolor : (color c G C e).isSome) :
  a ≠ color c G C e := by
  intro hc
  simp [edgeColorValid, freeColorsOn, incidentColorsOn] at hvalid
  rcases hvalid with h | h
  · rw [← Option.ne_none_iff_isSome] at hcolor
    rw [← hc, ← h] at hcolor
    contradiction
  · have aux1 : a ≠ none := by
      rcases h with ⟨⟨h, _⟩, _⟩
      rw [Option.ne_none_iff_isSome, Option.isSome_iff_exists]
      simp [allColors] at h
      rcases h with ⟨b, hb⟩
      use b; exact Eq.symm hb
    have aux2 : color c G C e ∈ C.val[e.1]'(by rw [C.sizeAx1]; exact e.1.isLt) := by
      simp [color]
    rcases h with ⟨⟨_, h⟩, ⟨_, _⟩⟩
    simp [aux1] at h
    unfold color at hc aux2
    rw [hc] at h
    contradiction

theorem setEdgeColor_freeOn (e : Edge n) (hpres : present G e) (a : Color c)
  (hvalid : edgeColorValid G C e a) (hcolor : (color c G C e).isSome) :
  color c G C e ∈ freeColorsOn G (setEdgeColor G C e a hpres hvalid) e.1 ∧
  color c G C e ∈ freeColorsOn G (setEdgeColor G C e a hpres hvalid) e.2 := by
  have hne := newColor_not_eq_oldColor G C e a hvalid hcolor
  simp [edgeColorValid] at hvalid
  simp_all [color, freeColorsOn, incidentColorsOn]
  have := C.validAx
  have hloop := edge_not_self_loop G e hpres
  have aux := set_set_spec3 n C.val C.sizeAx1 C.sizeAx2 a e.1 e.2 e.2 hloop
  repeat any_goals apply And.intro
  any_goals
    simp [allColors]
    apply Option.isSome_iff_exists.mp at hcolor
    rcases hcolor with ⟨a, ha⟩
    use a; exact Eq.symm ha
  · left
    specialize this e.1 e.2 hcolor
    apply Array.not_mem_of_count_eq_zero
    simp [setEdgeColor]
    rw [setEdge_spec5 G C e a hpres]
    split_ifs <;> simp_all
  · left
    specialize this e.2 e.1 (by simp_rw [← Fin.getElem_fin, C.symmAx e.1 e.2] at hcolor; assumption)
    apply Array.not_mem_of_count_eq_zero
    simp [setEdgeColor, setEdge]
    simp_rw [← Fin.getElem_fin, count_set_set, C.symmAx]
    simp_rw [Fin.getElem_fin] at *
    simp [← aux, this]
    simp_rw [← Fin.getElem_fin, C.symmAx e.1 e.2, Fin.getElem_fin] at hne
    exact hne


end EdgeColoring
