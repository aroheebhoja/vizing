import Std
import Mathlib.Tactic

set_option linter.unusedVariables false

namespace Aux

theorem pop_size_lt {α : Type} (A : Array α) (h : A ≠ #[]) :
  (A.pop).size < A.size := by
  simp only [Array.size_pop, tsub_lt_self_iff, zero_lt_one, and_true]
  exact Array.size_pos_iff.mpr h

theorem pop_back {α : Type} (A : Array α) (h : A ≠ #[]) (h' : A.size > 1)
  (hnodup : A.toList.Nodup) :
  A.back (Array.size_pos_iff.mpr h) ≠
  (A.pop).back (by simpa [pop_size_lt A h]) := by
  intro hc
  have : 0 < A.size := by linarith
  simp [Array.back] at hc
  have := @List.Nodup.getElem_inj_iff _ A.toList
        hnodup (A.size - 1) ?_
        (A.size - 1 - 1) ?_
  rw [Array.getElem_toList, Array.getElem_toList] at this
  rw [this] at hc
  apply Nat.eq_self_sub_one.mp at hc
  rw [← add_zero 1, ← hc] at h'
  simp at h'
  rw [Nat.sub_one, Nat.one_add, Nat.succ_pred] at h'
  all_goals simp_all
  exact Nat.sub_one_sub_lt_of_lt h'

end Aux
