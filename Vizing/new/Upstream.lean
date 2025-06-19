import Mathlib.Data.List.Lemmas
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

theorem nodup_subset_eq_length_le {α : Type} [DecidableEq α] (L M : List α)
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

theorem nodup_exists_mem_notMem_of_len_lt {α : Type} [DecidableEq α] (L M : List α)
  (hl : L.Nodup) (hm : M.Nodup) (hlen : L.length < M.length) :
  ∃ x ∈ M, x ∉ L := by
  rw [← List.toFinset_card_of_nodup hl, ← List.toFinset_card_of_nodup hm] at hlen
  apply Finset.exists_mem_notMem_of_card_lt_card at hlen
  simp_all

theorem count_gt_one_if {α : Type} [BEq α] [LawfulBEq α] (A : Array α) (n : Nat)
  (h : A.size = n) (i j : Fin n) :
  i ≠ j ∧ A[i] == A[j] → A.count (A[i]) > 1 := by
  intro ⟨h1, h2⟩
  simp_all [-Fin.getElem_fin]
  apply Lean.Omega.Fin.lt_or_gt_of_ne at h1
  wlog h' : i < j generalizing i j
  · specialize this j i (Eq.symm h2) (by tauto) (by tauto)
    rwa [h2] at this
  have aux2 : Array.count A[j] (A.take j) ≥ 1 := by
    simp [Array.mem_extract_iff_getElem]
    use i
    simp
    repeat constructor; assumption
    rw [h]; exact i.isLt
  have aux3 : Array.count A[j] (A.drop j) ≥ 1 := by
    simp [Array.mem_extract_iff_getElem]
    use 0
    simp
    rw [h]; exact j.isLt
  have : A.count A[j] = (A.take j ++ A.drop j).count A[j] := by
    congr
    simp [j.isLt, h]
    rw [← h]
    simp only [Array.extract_size]
  rw [this]
  rw [Array.count_append]
  linarith
