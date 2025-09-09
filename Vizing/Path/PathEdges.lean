import Vizing.Path.Defs

namespace Path
open Graph
open EdgeColoring
open Aux

variable {n c : Nat} {G : Graph n} {C : EdgeColoring c G}
  {a b : Color c} (ha : a.isSome) (hb : b.isSome)
  {x : Vertex n} (P : Path C a b x)
  (hfree : b ∈ freeColorsOn C x)

def pathEdges :=
  allAdjacentPairs P.val

theorem color_of_mem_pathEdges {e : Edge n} {P : Path C a b x} (h : e ∈ pathEdges P) :
  color C e = a ∨ color C e = b := by
  rw [pathEdges, mem_allAdjacentPairs_iff_adjacent] at h
  have := P.colorAx
  unfold alternatesColor at this
  apply chain'_of_alternates at this
  rcases h with ⟨i, _, _, _⟩ | ⟨i, _, _, _⟩
  all_goals
  have := @chain'_rel_of_idx_consec _ _ P.val i (i + 1) (by omega) (by omega) this (by rfl)
  simp_all [color_symm]

include ha hb in
theorem color_isSome_of_mem_pathEdges {e : Edge n} {P : Path C a b x} (h : e ∈ pathEdges P) :
  (color C e).isSome := by
  apply color_of_mem_pathEdges at h
  rcases h with h | h <;> (subst h; assumption)

include ha hb in
theorem exists_other_nbor_of_mem_pathEdges {u v : Vertex n} {P : Path C a b x}
  (h1 : (u, v) ∈ pathEdges P) (h2 : u ≠ P.val.head P.nonemptyAx ∧ u ≠ P.val.getLast P.nonemptyAx) :
  ∃ w, (u, w) ∈ pathEdges P ∧ color C (u, w) ≠ color C (u, v) := by
  have hsome := color_isSome_of_mem_pathEdges ha hb h1
  rw [pathEdges, mem_allAdjacentPairs_iff_adjacent] at h1
  simp [List.head_eq_getElem, List.getLast_eq_getElem] at h2
  rcases h1 with ⟨i, hi, hu, hv⟩ | ⟨i, hi, hv, hu⟩
  all_goals subst hu hv
  use P.val[i - 1]
  have aux : (P.val[i], P.val[i - 1]) ∈ pathEdges P := by
    rw [pathEdges, mem_allAdjacentPairs_iff_adjacent]
    right
    use i - 1, (by omega)
    simp_all
    congr
    have : i ≠ 0 := by contrapose! h2; simp [h2]
    omega
  constructor
  · assumption
  · by_contra hc
    apply color_unique at hc
    apply color_isSome_of_mem_pathEdges at aux
    rcases hc with hc | hc <;> simp_all [List.Nodup.getElem_inj_iff P.nodupAx]
    repeat assumption
  · have : i + 2 < P.val.length := by
      apply Nat.add_lt_of_lt_sub
      have : i ≠ P.val.length - 2 := by
        by_contra hc; subst hc
        simp [List.Nodup.getElem_inj_iff P.nodupAx] at h2
        apply h2
        omega
      omega
    use P.val[i + 2]
    have aux : (P.val[i + 1], P.val[i + 2]) ∈ pathEdges P := by
      rw [pathEdges, mem_allAdjacentPairs_iff_adjacent]
      left
      use i+1, (by omega)
    constructor
    · assumption
    · by_contra hc
      apply color_unique at hc
      apply color_isSome_of_mem_pathEdges at aux
      rcases hc with hc | hc <;> simp_all [List.Nodup.getElem_inj_iff P.nodupAx]
      repeat assumption

include ha hb hfree in
theorem mem_path_of_color_aux {L : List (Vertex n)} (h1 : L ≠ [])
  (h2 : L[0]'(by exact List.length_pos_iff.mpr h1) = x)
  (h3 : alternatesColor C L a b)
  (h4 : next a b L ∈ freeColorsOn C (L.getLast h1))
  {u v : Vertex n} (h5 : u ∈ L)
  (h : color C (u, v) = a ∨ color C (u, v) = b) :
  (u, v) ∈ allAdjacentPairs L := by
  unfold alternatesColor at h3
  apply not_exists_of_freeColor at hfree
  have hsome : color C (u, v) ≠ none := by
    rcases h with h | h <;> simp_all [Option.isSome_iff_ne_none]
  rcases List.getElem_of_mem h5 with ⟨i, hi1, hi2⟩
  have : i = 0 ∨ (0 < i ∧ i < L.length - 1) ∨ i = L.length - 1 := by omega
  rcases this with this | this | this
  · subst this
    unfold alternates at h3
    split at h3 <;> simp_all [next, allAdjacentPairs]
    · apply not_exists_of_freeColor at h4
      simp_all
    · left
      subst hi2
      rw [← h3.left] at h
      apply color_unique_of_isSome at h <;> simp_all
  · have := middle_spec h3 i this
    rw [mem_allAdjacentPairs_iff_adjacent]
    rcases this with this | this
    · rcases h with h | h
      · rw [← this.left, hi2, color_symm _ L[i - 1]] at h
        apply color_unique_of_isSome at h
        right
        use i - 1, (by omega)
        grind
        simpa [Option.isSome_iff_ne_none]
      · rw [← this.right, hi2] at h
        apply color_unique_of_isSome at h
        left
        use i, (by omega)
        simp_all
        simpa [Option.isSome_iff_ne_none]
    · rcases h with h | h
      · rw [← this.right, hi2] at h
        apply color_unique_of_isSome at h
        left
        use i, (by omega)
        simp_all
        simpa [Option.isSome_iff_ne_none]
      · rw [← this.left, hi2, color_symm _ L[i - 1]] at h
        apply color_unique_of_isSome at h
        right
        use i - 1, (by omega)
        grind
        simpa [Option.isSome_iff_ne_none]
  · subst this
    rw [List.getLast_eq_getElem] at h4
    by_cases h : L.length = 1
    · have : L = [x] := by
        apply List.length_eq_one_iff.mp at h
        grind
      apply not_exists_of_freeColor at h4
      simp_all [next]
    · rw [mem_allAdjacentPairs_iff_adjacent]
      rcases next_eq_a_or_b a b L with hnext | hnext
      · have := last_b_of_next_a _ a b L (by grind) h3 hnext
        have aux : color C (u, v) = b := by
          rw [hnext] at h4
          apply not_exists_of_freeColor at h4
          rw [← hi2]
          simp_all
        subst hi2
        simp_rw [color_symm, ← aux] at this
        apply color_unique_of_isSome at this
        right
        · use L.length - 2, (by omega)
          simp_all
          congr; omega
        simp_all
      · have := last_a_of_next_b _ a b L (by grind) h3 hnext
        have aux : color C (u, v) = a := by
          rw [hnext] at h4
          apply not_exists_of_freeColor at h4
          rw [← hi2]
          simp_all
        subst hi2
        simp_rw [color_symm, ← aux] at this
        apply color_unique_of_isSome at this
        right
        · use L.length - 2, (by omega)
          simp_all
          congr; omega
        simp_all

include ha hb hfree in
theorem mem_path_of_color {P : Path C a b x} {u v : Vertex n}
  (h : u ∈ P.val) (h2 : color C (u, v) = a ∨ color C (u, v) = b)
  (h3 : isMaximalPath P) :
  (u, v) ∈ pathEdges P := by
  exact mem_path_of_color_aux ha hb hfree P.nonemptyAx P.firstElemAx P.colorAx h3 h h2
