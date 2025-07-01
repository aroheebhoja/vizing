import Mathlib.Data.List.Lemmas
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Aux

-- Read mathlib guidelines

theorem length_le_length_of_nodup_of_subset {α : Type} [DecidableEq α] {L M : List α}
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

theorem exists_mem_notMem_of_nodup_of_len_lt {α : Type} [DecidableEq α] {L M : List α}
  (hl : L.Nodup) (hm : M.Nodup) (hlen : L.length < M.length) :
  ∃ x ∈ M, x ∉ L := by
  rw [← List.toFinset_card_of_nodup hl, ← List.toFinset_card_of_nodup hm] at hlen
  apply Finset.exists_mem_notMem_of_card_lt_card at hlen
  simp_all

theorem dropLast_nodup_of_nodup {α : Type} [DecidableEq α] {L : List α}
    (hl : L.Nodup) : L.dropLast.Nodup :=
  List.Sublist.nodup (List.dropLast_sublist L) hl

theorem back_of_back? {α : Type} {A : Array α} {a : α} (h : A.back? = some a) :
  ∃ h, A.back h = a := by
    use Array.size_pos_iff.mpr (Array.back?_isSome.mp
      (Option.isSome_of_eq_some h))
    rw [Array.back]
    rw [Array.back?] at h
    exact Array.getElem_eq_iff.mpr h

theorem chain'_rel {α : Type u} {R : α → α → Prop}
  {l : List α} {b : α}
  (h1 : List.Chain' R l) (h2 : b ∈ l) (h3 : l ≠ [])
  (h4 : l[0]'(List.length_pos_iff.mpr h3) ≠ b) : ∃ a ∈ l, R a b := by
  rcases List.getElem_of_mem h2 with ⟨i, hlen, hi⟩
  subst hi
  have aux : 1 ≤ i := by
    apply Nat.one_le_iff_ne_zero.mpr
    contrapose! h4
    simp_rw [h4]
  use l[i - 1]
  constructor
  · apply List.getElem_mem
  · apply List.chain'_iff_get.mp at h1
    specialize h1 (i - 1) ?_
    · apply Nat.sub_lt_sub_right aux hlen
    · simpa [List.get_eq_getElem, Nat.sub_add_cancel aux] using h1

theorem chain'_rel' {α : Type u} {R : α → α → Prop}
  {l : List α} {a : α}
  (h1 : List.Chain' R l) (h2 : a ∈ l) (h3 : l ≠ [])
  (h4 : l.getLast h3 ≠ a) : ∃ b ∈ l, R a b := by
  rcases List.getElem_of_mem h2 with ⟨i, hlen, hi⟩
  subst hi
  have : i < l.length - 1 := by
    rw [← Ne.le_iff_lt]
    exact Nat.le_sub_one_of_lt hlen
    contrapose! h4
    subst h4
    rw [List.getLast_eq_getElem]
  use l[i + 1]
  constructor
  · apply List.getElem_mem
  · apply List.chain'_iff_get.mp at h1
    specialize h1 i this
    assumption

theorem chain'_rel_of_idx_consec {α : Type u} {R : α → α → Prop}
  {l : List α} {i j : Nat} (hi : i < l.length) (hj : j < l.length)
  (h1 : List.Chain' R l) (h2 : j = i + 1) :
  (R l[i] l[j]) := by
  subst h2
  apply List.chain'_iff_get.mp h1
  exact Nat.lt_sub_of_add_lt hj

theorem chain'_exists_mem_notMem_of_nodup_prefix_length_lt
  {α : Type} {R : α → α → Prop}
  {l l₁ : List α} (h1 : l₁ <+: l) (h2 : l₁.length < l.length) (h3 : l₁ ≠ [])
  (h4 : List.Chain' R l) (h5 : l.Nodup) :
   ∃ b ∈ l, b ∉ l₁ ∧ R (l₁.getLast h3) b ∧ b = l[l₁.length] := by
  have aux := List.getLast_eq_getElem h3
  use l[l₁.length]
  repeat any_goals apply And.intro
  · exact List.getElem_mem h2
  · by_contra hc
    apply List.getElem_of_mem at hc
    rcases hc with ⟨i, hi, hc⟩
    rw [List.IsPrefix.getElem h1] at hc
    rw [List.Nodup.getElem_inj_iff] at hc
    · apply ne_of_lt at hi
      contradiction
    · assumption
  · rw [aux, List.IsPrefix.getElem h1]
    apply chain'_rel_of_idx_consec _ _ h4
    apply (Nat.sub_eq_iff_eq_add ?_).mp rfl
    apply Nat.one_le_iff_ne_zero.mpr
    exact Nat.ne_zero_of_lt (List.length_pos_of_ne_nil h3)
  · rfl

theorem chain'_prefix {α : Type u} {R S : α → α → Prop}
  {l l₁ : List α} (h1 : l₁ <+: l) (h2 : ∀ a b, a ∈ l₁ ∧ b ∈ l₁ → R a b → S a b)
  (h3 : List.Chain' R l) : List.Chain' S l₁ := by
  have : List.Chain' R l₁ := List.Chain'.prefix h3 h1
  rw [List.chain'_iff_get] at ⊢ this
  intro i h
  apply h2
  · constructor <;> apply List.get_mem
  · exact this i h

theorem getLast_not_mem_dropLast_of_nodup {α : Type u} {l : List α}
  (h1 : l ≠ []) (h2 : l.Nodup) : (l.getLast h1) ∉ l.dropLast := by
  apply List.Nodup.notMem
  apply (@List.nodup_rotate _ _ 1).mp
  simpa [List.dropLast_concat_getLast]

theorem one_lt_count {α : Type} [BEq α] [LawfulBEq α] {A : Array α}
  {i j : Fin A.size} (h1 : i ≠ j) (h2 : A[i] == A[j]) :
   1 < A.count (A[i]) := by
  apply Lean.Omega.Fin.lt_or_gt_of_ne at h1
  rw [beq_iff_eq] at h2
  wlog h' : i < j generalizing i j
  · specialize @this j i (Eq.symm h2) (by tauto) (by tauto)
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
