import Vizing.new.Fan

set_option linter.dupNamespace false
set_option push_neg.use_distrib true
-- set_option trace.profiler true

namespace Subfan
open Graph
open Nbhd
open EdgeColoring
open Fan

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

/-

If F is a strict subfan of G, there exists an element we can add to F
to create a larger fan.

That is, there is a vertex z adjacent to x such that the color of (x, z) is free on F.back.

Prefix -> equal or there exists another element we can add

That element is adjacent to

-/

theorem maximalFan_spec : ∀ (F : Fan G C x y),
  isSubfan G C x y (maximalFan G C x y h) F →
  F.val = (maximalFan G C x y h).val := by
  intro F hF
  simp [isSubfan, ← Array.isPrefixOf_toList] at hF
  rcases (lt_or_eq_of_le (List.IsPrefix.length_le hF)) with hlt | heq
  · exfalso
    have hsize := (Array.size_pos_iff.mpr (maximalFan G C x y h).nonemptyAx)
    have ⟨_, aux0⟩ := List.prefix_iff_getElem.mp hF

    apply List.prefix_iff_eq_append.mp at hF
    rw [List.drop_eq_getElem_cons hlt] at hF

    have := F.colorAx
    simp [colorAx] at this
    specialize this ((maximalFan G C x y h).val.toList.length - 1) (by simp; apply Nat.sub_lt_sub_right hsize hlt)
    simp at this;

    have aux : (maximalFan G C x y h).val.size - 1 + 1 = (maximalFan G C x y h).val.size := by
      apply Nat.sub_add_cancel hsize
    simp_rw [aux] at this

    specialize aux0 ((maximalFan G C x y h).val.toList.length - 1) (Nat.sub_one_lt (Nat.ne_zero_of_lt hsize))
    simp at aux0
    rw [← aux0] at this
    

    have := add_maximal G C x y (default G C x y h).val ((nbhd G x).val.erase y) (default G C x y h).nonemptyAx
    simp [Array.back] at this
    specialize this F.val[(maximalFan G C x y h).val.size] (by sorry )
    simp_all [maximalFan, mkMaxFan]
  · apply Array.toList_inj.mp
    apply List.IsPrefix.eq_of_length_le
    simp_all
    sorry
    exact Nat.le_of_eq heq

end Subfan
