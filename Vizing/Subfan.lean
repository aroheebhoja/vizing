import Vizing.Fan
import Vizing.TakeUntil

set_option linter.dupNamespace false
set_option push_neg.use_distrib true

namespace Fan
open Graph
open EdgeColoring
open Aux

/-

Definition of a subfan:

H is a subfan of F if H is a fan such that H.val is a prefix of F.val.

Proof that maximalFan is a maximal fan

-/

variable {n c : Nat} (G : Graph n) (C : EdgeColoring c G) (x y : Vertex n)
  (h : present G (x, y))

-- F1 is a subfan of F2
def isSubfan (F1 F2 : Fan G C x y) :=
  F1.val.isPrefixOf F2.val

theorem maximalFan_spec : ∀ (F : Fan G C x y),
  isSubfan G C x y (maximalFan G C x y h) F →
  F.val = (maximalFan G C x y h).val := by
  intro F hF
  simp [isSubfan, ← Array.isPrefixOf_toList] at hF
  rcases (lt_or_eq_of_le (List.IsPrefix.length_le hF)) with hlt | heq
  · have ⟨_, hF'⟩ := List.prefix_iff_getElem.mp hF
    rw [List.prefix_iff_eq_append, List.drop_eq_getElem_cons hlt] at hF
    have hsize := (Array.size_pos_iff.mpr (maximalFan G C x y h).nonemptyAx)
    specialize hF' ((maximalFan G C x y h).val.toList.length - 1)
      (Nat.sub_one_lt (Nat.ne_zero_of_lt hsize))
    have hcolor := F.colorAx ((maximalFan G C x y h).val.toList.length - 1)
      (by simp; apply Nat.sub_lt_sub_right hsize hlt)
    simp at hF' hcolor
    simp_rw [Nat.sub_add_cancel hsize, ← hF'] at hcolor
    contrapose! hcolor
    simp [maximalFan]
    apply mkMaxFan_maximal
    all_goals simp_all only [maximalFan]
    · apply (List.mem_erase_of_ne ?_).mpr
      · apply F.nborsAx
        apply Array.getElem_mem_toList
      · simp_rw [← F.firstElemAx]
        have hc := (maximalFan G C x y h).nonemptyAx
        simp [maximalFan, ← F.firstElemAx] at hc
        contrapose! hc
        apply (List.Nodup.getElem_inj_iff F.nodupAx).mp at hc
        exact Array.eq_empty_of_size_eq_zero hc
    · have h := F.nodupAx
      rw [← hF, List.nodup_middle] at h
      apply List.Nodup.notMem at h
      simp at h
      exact h.left
  · apply Array.toList_inj.mp
    apply Eq.symm
    apply List.IsPrefix.eq_of_length_le
    simp_all
    exact Nat.le_of_eq (Eq.symm heq)

def findSubfanWithColor (F : Fan G C x y) (a : Color c) : Fan G C x y where
  val := takeUntil (a ∉ freeColorsOn G C ·) F.val
  nborsAx := by
    intro v hv
    apply F.nborsAx
    apply List.IsPrefix.mem hv
    rw [← List.isPrefixOf_iff_prefix, Array.isPrefixOf_toList]
    exact takeUntil_prefix (a ∉ freeColorsOn G C ·) F.val
  nonemptyAx := by
    simp [takeUntil]
    exact F.nonemptyAx
  firstElemAx := by
    simp [takeUntil]
    exact F.firstElemAx
  colorAx := by
    simp [colorAx, takeUntil]
    intro i h
    apply F.colorAx
    simp_rw [← Nat.pred_eq_sub_one, ← Nat.pred_min_pred] at h
    simp at h
    exact h.right
  nodupAx := by
    apply List.Sublist.nodup ?_ F.nodupAx
    apply List.IsPrefix.sublist
    rw [← List.isPrefixOf_iff_prefix, Array.isPrefixOf_toList]
    exact takeUntil_prefix (a ∉ freeColorsOn G C ·) F.val

end Fan
