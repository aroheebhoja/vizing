import Vizing.Graph
import Vizing.EdgeColoring.SetColor

namespace EdgeColoring
open Graph
open Aux

variable {n : Nat} {c : Nat} {G : Graph n} (C : EdgeColoring c G)


theorem incidentColors_invariant (e : Edge n) (a : Color c)
  (hpres : present G e) (hvalid : edgeColorValid C e a) :
  ∀ v : Vertex n, v ≠ e.1 ∧ v ≠ e.2 → incidentColorsOn C v =
    incidentColorsOn (setEdgeColor C e a hpres hvalid) v := by
  intro v _
  simp [incidentColorsOn, setEdgeColor]
  have := setEdge_spec4 C e a v (by tauto)
  rw [this]

theorem freeColors_invariant (e : Edge n) (a : Color c)
  (hpres : present G e) (hvalid : edgeColorValid C e a) :
  ∀ v : Vertex n, v ≠ e.1 ∧ v ≠ e.2 → freeColorsOn C v =
    freeColorsOn (setEdgeColor C e a hpres hvalid) v := by
  intro v h
  simp only [freeColorsOn]
  rw [incidentColors_invariant C e a hpres hvalid v h]

theorem color_invariant (e : Edge n) (a : Color c)
  (hpres : present G e) (hvalid : edgeColorValid C e a) :
  ∀ f : Edge n, f ≠ e ∧ f ≠ (e.2, e.1) →
  color C f = color (setEdgeColor C e a hpres hvalid) f := by
  intro f h
  simp [setEdgeColor]
  apply setEdge_spec3
  simp_rw [ne_eq, Prod.eq_iff_fst_eq_snd_eq] at h
  tauto

theorem existsFreeColor (h : ↑(maxDegree G) < c) :
  ∀ v : Vertex n, (freeColorsOn C v) ≠ [] := by
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
    have hlt : (coloredNbors C v).val.length < c := by
      have h1 := colored_nbhd_size_le C v
      have h2 := maxDegree_spec G v
      exact lt_of_le_of_lt (le_trans h1 h2) h
    have hle : (List.filter Option.isSome
      (List.map (fun x ↦ color C (v, x))
      (coloredNbors C v).val)).length ≤
      (coloredNbors C v).val.length := by
      have := List.length_filter_le Option.isSome
            (List.map (fun x ↦ color C (v, x)) (coloredNbors C v).val)
      rw [List.length_map] at this
      exact this
    exact Nat.lt_of_le_of_lt hle hlt

theorem newColor_not_eq_oldColor (e : Edge n) (a : Color c)
  (hvalid : edgeColorValid C e a) (hcolor : (color C e).isSome) :
  a ≠ color C e := by
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
    have aux2 : color C e ∈ C.val[e.1]'(by rw [C.sizeAx1]; exact e.1.isLt) := by
      simp [color]
    rcases h with ⟨⟨_, h⟩, ⟨_, _⟩⟩
    simp [aux1] at h
    unfold color at hc aux2
    rw [hc] at h
    contradiction

theorem setEdgeColor_freeOn (e : Edge n) (hpres : present G e) (a : Color c)
  (hvalid : edgeColorValid C e a) (hcolor : (color C e).isSome) :
  color C e ∈ freeColorsOn (setEdgeColor C e a hpres hvalid) e.1 ∧
  color C e ∈ freeColorsOn (setEdgeColor C e a hpres hvalid) e.2 := by
  have hne := newColor_not_eq_oldColor C e a hvalid hcolor
  simp [edgeColorValid] at hvalid
  simp_all [color, freeColorsOn, incidentColorsOn]
  have := C.validAx
  have hloop := edge_not_self_loop e hpres
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
    rw [setEdge_spec5 C e a hpres]
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

theorem color_unique (u v₁ v₂ : Vertex n) :
  color C (u, v₁) = color C (u, v₂) →
  (color C (u, v₁)).isNone ∨ v₁ = v₂ := by
  intro h
  simp [color] at h
  by_cases heq : v₁ = v₂
  · right; assumption
  · simp_all only [Option.isNone_iff_eq_none, or_false]
    apply beq_iff_eq.mpr at h
    have h1 := v₁.prop
    have h2 := v₂.prop
    simp_rw [← C.sizeAx2 u] at h1 h2
    have hc := @one_lt_count _ _ _ _ ⟨v₁, h1⟩ ⟨v₂, h2⟩ ?_ h
    · simp at hc
      have := C.validAx u v₁
      contrapose! this
      constructor
      · exact Option.isSome_iff_ne_none.mpr this
      · exact Ne.symm (Nat.ne_of_lt hc)
    · simp only [Fin.getElem_fin, ne_eq, Fin.mk.injEq]
      exact Fin.val_ne_of_ne heq

theorem color_symm (v₁ v₂ : Vertex n) :
  color C (v₁, v₂) = color C (v₂, v₁) := by
  simp only [color]
  exact C.symmAx v₁ v₂

def findNborWithColor (v : Vertex n) (a : Color c) : Option (Vertex n) :=
  (nbhd G v).val.find? (fun v' => color C (v, v') = a)

end EdgeColoring
