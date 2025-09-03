import Vizing.Path.Defs

namespace Path
open Graph
open EdgeColoring
open Aux

variable {n c : Nat} {G : Graph n} {C : EdgeColoring c G}
  {a b : Color c} (ha : a.isSome) (hb : b.isSome)
  {x : Vertex n} (P : Path C a b x)

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
