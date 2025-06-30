import Mathlib.Data.List.Lemmas
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Aux

-- Read mathlib guidelines

theorem length_le_length_of_nodup_of_subset {α : Type} [DecidableEq α] (L M : List α)
  (hl : L.Nodup) (hsubset : L ⊆ M) : L.length ≤ M.length := by
  have h1 : L ⊆ M.dedup := by
    exact fun _ x ↦ List.subset_dedup M (hsubset x)
  have h2 : M.dedup.length ≤ M.length := by
    apply List.Sublist.length_le
    exact List.dedup_sublist M
  have h3 : L.length ≤ M.dedup.length := by
    have := List.nodup_dedup M
    rw [← List.toFinset_card_of_nodup hl,
        ← List.toFinset_card_of_nodup (List.nodup_dedup M)]
    apply Finset.card_le_card
    repeat any_goals rw [← List.toFinset_eq]
    repeat assumption
  exact le_trans h3 h2

theorem exists_mem_notMem_of_nodup_of_len_lt {α : Type} [DecidableEq α] (L M : List α)
  (hl : L.Nodup) (hm : M.Nodup) (hlen : L.length < M.length) :
  ∃ x ∈ M, x ∉ L := by
  rw [← List.toFinset_card_of_nodup hl, ← List.toFinset_card_of_nodup hm] at hlen
  apply Finset.exists_mem_notMem_of_card_lt_card at hlen
  simp_all

theorem dropLast_nodup_of_nodup {α : Type} [DecidableEq α] {L : List α}
    (hl : L.Nodup) : L.dropLast.Nodup :=
  List.Sublist.nodup (List.dropLast_sublist L) hl

theorem one_lt_count {α : Type} [BEq α] [LawfulBEq α] (A : Array α)
  (i j : Fin A.size) (h1 : i ≠ j) (h2 : A[i] == A[j]) :
   1 < A.count (A[i]) := by
  apply Lean.Omega.Fin.lt_or_gt_of_ne at h1
  rw [beq_iff_eq] at h2
  wlog h' : i < j generalizing i j
  · specialize this j i (Eq.symm h2) (by tauto) (by tauto)
    rwa [← h2] at this
  have aux1 : 1 ≤ Array.count A[j] (A.take j) := by
    simp only [Array.take_eq_extract, Array.one_le_count_iff,
    Array.mem_extract_iff_getElem]
    use i
    simp_all
  have aux2 : 1 ≤ Array.count A[j] (A.drop j) := by
    simp only [Array.drop_eq_extract, Array.one_le_count_iff,
    Array.mem_extract_iff_getElem]
    use 0
    simp
  have : A.count A[j] = (A.take j ++ A.drop j).count A[j] := by
    congr
    simp_all [j.isLt, Array.extract_size]
  rw [h2, this, Array.count_append]
  linarith

end Aux
