import Vizing.Graph
import Vizing.EdgeColoring.Defs

namespace EdgeColoring
open Graph
open Aux

variable {n : Nat} {c : Nat} {G : Graph n} (C : EdgeColoring c G)

theorem nbhd_to_indexed_nbhd (v : Vertex n) (A : Array (Array (Color c)))
  (h1 : A.size = n) (h2 : ∀ i : Fin n, A[i].size = n) :
  A[v].toList = List.map (fun x ↦ A[v][x]'(by simp_all)) (List.finRange n) := by
  ext1 i
  simp [Option.map]; split
  all_goals rename_i j hj
  · apply Array.getElem?_eq_some_iff.mpr
    rcases (List.getElem?_eq_some_iff.mp hj) with ⟨h3, h4⟩
    have : i < A[v].size := by
      rw [h2]
      rwa [List.length_finRange] at h3
    use this
    congr
    simp at h4
    exact Fin.mk.inj_iff.mp h4
  · apply Array.getElem?_eq_none_iff.mpr
    have := List.getElem?_eq_none_iff.mp hj
    rw [List.length_finRange] at this
    simp_all

theorem incident_colors_of_colored_nbors (v : Vertex n) :
  incidentColorsOn C v =
  List.filter Option.isSome
  ((coloredNbors C v).val.map (fun x => color C (v, x))) := by
  simp_all [incidentColorsOn, coloredNbors, color]
  have := nbhd_to_indexed_nbhd v C.val C.sizeAx1 C.sizeAx2
  simp_all [List.filter_map]
  congr

theorem colored_nbors_subset_nbors (v : Vertex n) :
  (coloredNbors C v).val ⊆ (nbhd G v).val := by
  simp [coloredNbors]
  intro x h'
  have := C.representsEdgesAx (v, x)
  simp_all [present]

theorem colored_nbhd_size_le (v : Vertex n) :
  (coloredNbors C v).val.length ≤ degree G v := by
  let N := coloredNbors C v
  let X := nbhd G v
  simp [degree]
  apply length_le_length_of_nodup_of_subset
  · exact N.nodupAx
  · exact colored_nbors_subset_nbors C v

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

theorem color_neq (u v₁ v₂ : Vertex n)
  (h1 : (color C (u, v₁)).isSome) (h2 : v₁ ≠ v₂) :
  color C (u, v₁) ≠ color C (u, v₂) := by
  by_contra h
  apply color_unique at h
  simp_all

theorem color_unique_of_isSome (u v₁ v₂ : Vertex n)
  (h1 : (color C (u, v₁)).isSome) :
  color C (u, v₁) = color C (u, v₂) → v₁ = v₂ := by
  intro h
  apply color_unique at h
  apply (Or.resolve_left h)
  simp only [Option.isNone_iff_eq_none]
  exact Option.isSome_iff_ne_none.mp h1

theorem color_symm (v₁ v₂ : Vertex n) :
  color C (v₁, v₂) = color C (v₂, v₁) := by
  simp only [color]
  exact C.symmAx v₁ v₂

end EdgeColoring
