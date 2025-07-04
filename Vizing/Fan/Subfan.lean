import Vizing.Fan.Maximal

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

variable {n c : Nat} {G : Graph n} (C : EdgeColoring c G) {x y : Vertex n}
  (h : present G (x, y))

-- F1 is a subfan of F2
def isSubfan (F1 F2 : Fan C x y) :=
  F1.val.isPrefixOf F2.val

theorem maximalFan_spec : ∀ (F : Fan C x y),
  isSubfan C (maximalFan C h) F →
  F.val = (maximalFan C h).val := by
  intro F hF
  simp [isSubfan, ← Array.isPrefixOf_toList] at hF
  rcases (lt_or_eq_of_le (List.IsPrefix.length_le hF)) with hlt | heq
  · have := chain'_mem_notMem_of_nodup_prefix_length_lt
      hF hlt (by simp; exact (maximalFan C h).nonemptyAx) F.colorAx F.nodupAx
    rcases this with ⟨h1, h2⟩
    have := mkMaxFan_maximal C h
    contrapose! this
    simp [fan_prop, maximalFan] at h1 h2 ⊢
    use F.val[(mkMaxFan C h).size]
    repeat any_goals apply And.intro
    · apply (List.mem_erase_of_ne ?_).mpr
      · exact F.nborsAx (by simp)
      · simp_rw [← F.firstElemAx]
        by_contra hc
        apply (maximalFan C h).nonemptyAx
        apply (List.Nodup.getElem_inj_iff F.nodupAx).mp at hc
        simp_rw [← Array.size_eq_zero_iff.mp hc, maximalFan]
        congr
        exact Eq.symm F.firstElemAx
    repeat assumption
  · apply Array.toList_inj.mp
    apply Eq.symm
    apply List.IsPrefix.eq_of_length_le
    simp_all
    exact Nat.le_of_eq (Eq.symm heq)

def findSubfanWithColor (F : Fan C x y) (a : Color c) : Fan C x y where
  val := takeUntil (a ∉ freeColorsOn C ·) F.val
  nborsAx := by
    intro v hv
    apply F.nborsAx
    apply List.IsPrefix.mem hv
    rw [← List.isPrefixOf_iff_prefix, Array.isPrefixOf_toList]
    exact takeUntil_prefix (a ∉ freeColorsOn C ·) F.val
  nonemptyAx := by
    simp [takeUntil]
    exact F.nonemptyAx
  firstElemAx := by
    simp [takeUntil]
    exact F.firstElemAx
  colorAx := by
    simp [colorAx]
    apply List.Chain'.prefix (l := F.val.toList)
    · exact F.colorAx
    · simp [← List.isPrefixOf_iff_prefix, Array.isPrefixOf_toList]
      apply takeUntil_prefix
  nodupAx := by
    apply List.Sublist.nodup ?_ F.nodupAx
    apply List.IsPrefix.sublist
    rw [← List.isPrefixOf_iff_prefix, Array.isPrefixOf_toList]
    exact takeUntil_prefix (a ∉ freeColorsOn C ·) F.val

end Fan
