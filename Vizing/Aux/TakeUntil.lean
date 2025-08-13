import Std
import Mathlib.Data.List.Lemmas
import Mathlib.Tactic

/-

Given an array A and a predicate p, takeUntil will return the prefix of A
up to *and including* the first element that does not satisfy p.

If every element in the array satisfies p, takeUntil p A = A.

So, takeUntil p A = if takeWhile p A ≠ A then
  takeWhile p A ++ A[(takeWhile p A).size] else
  takeWhile p A

-/

namespace Aux

def takeUntil {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool) (A : Array α) :=
  A.extract 0 (A.findIdx (!p ·) + 1)

theorem takeUntil_prefix {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool) (A : Array α) :
  (takeUntil p A).isPrefixOf A := by
  rw [takeUntil, ← Array.isPrefixOf_toList]
  simp
  exact List.take_prefix (Array.findIdx (fun x ↦ !p x) A + 1) A.toList

theorem takeUntil_spec {α : Type} [BEq α] [LawfulBEq α]
  (p : α → Bool) (A : Array α) (i : Fin (takeUntil p A).size) :
  i < (takeUntil p A).size - 1 → p (takeUntil p A)[i] := by
  intro h
  by_cases ha : Array.findIdx (!p ·) A = A.size
  · simp [takeUntil, ha]
    have := Array.findIdx_eq_size.mp ha
    simp at this; apply this
    exact Array.mem_of_getElem rfl
  · simp [takeUntil]
    have aux : ∀ x ∈ A.takeWhile p, p x := by
      rw [List.takeWhile_toArray]
      simp only [Array.mem_toArray]
      intro x h
      apply List.mem_takeWhile_imp at h
      assumption
    apply aux
    simp_rw [Array.takeWhile_eq_extract_findIdx_not]
    apply Array.mem_extract_iff_getElem.mpr
    use i
    constructor
    · simp_all
      have := Array.getElem_extract i.isLt
      simp only [zero_add, ← Fin.getElem_fin] at this
      exact Eq.symm this
    · simp_all [takeUntil]
      rw [← Nat.pred_eq_sub_one, ← Nat.pred_min_pred] at h
      simp at h
      rcases h with ⟨l, r⟩
      constructor
      all_goals omega

theorem takeUntil_spec' {α : Type} [BEq α] [LawfulBEq α]
  (p : α → Bool) (A : Array α) (i : Fin (takeUntil p A).size) :
  i = (takeUntil p A).size - 1 → p (takeUntil p A)[i] = false := by
  intro h
  simp [takeUntil] at ⊢ h


  sorry

end Aux
