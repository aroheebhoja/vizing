import Vizing.Aux
import Vizing.Graph
import Vizing.EdgeColoring
import Vizing.Fan
import Vizing.Path

open Aux Graph EdgeColoring Fan Path

variable
  {n c : Nat} {G : Graph n} (C : EdgeColoring c G)
  {x y : Vertex n} {a b : Color c}

-- Maximality : all free colors on last vertex of fan are free on x

theorem inversion_guarantee (F : Fan C x y)
  {C' : EdgeColoring c G}
  {P : Path C a b x}
  (hC' : isInverted C C' P) :
  ∃ i : Fin F.val.size, a ∈ freeColorsOn C' F.val[i] := by
  by_cases h : ∃ j : Fin F.val.size, color C (x, F.val[j]) = a
  rcases h with ⟨j, hj⟩
  have : j.val > 0 := by
    by_contra hc
    simp at hc
    simp [hc, F.firstElemAx] at hj
    sorry
  sorry
  have aux1 : a ∈ freeColorsOn C x := by sorry
  have aux2 : P.val = [x] := by sorry
  have aux3 : C' = C := by sorry
  rw [aux3]
  use ⟨F.val.size - 1, (by simp; apply Array.size_pos_iff.mpr; exact F.nonemptyAx)⟩
  sorry

def findSubfanWithColor (F : Fan C x y)
  (C' : EdgeColoring c G)
  (P : Path C a b x)
  (h : isInverted C C' P) : Fan C' x y where
  val := takeUntil (a ∉ freeColorsOn C' ·) F.val
  nborsAx := by
    intro v hv
    apply F.nborsAx
    apply List.IsPrefix.mem hv
    rw [← List.isPrefixOf_iff_prefix, Array.isPrefixOf_toList]
    exact takeUntil_prefix (a ∉ freeColorsOn C' ·) F.val
  nonemptyAx := by
    simp [takeUntil]
    exact F.nonemptyAx
  firstElemAx := by
    simp [takeUntil]
    exact F.firstElemAx
  colorAx := by
    simp [colorAx]
    apply List.Chain'.prefix (l := F.val.toList)
    · unfold fan_prop
      -- Path inversion guarantee
      sorry
    · simp [← List.isPrefixOf_iff_prefix, Array.isPrefixOf_toList]
      apply takeUntil_prefix
  nodupAx := by
    apply List.Sublist.nodup ?_ F.nodupAx
    apply List.IsPrefix.sublist
    rw [← List.isPrefixOf_iff_prefix, Array.isPrefixOf_toList]
    exact takeUntil_prefix (a ∉ freeColorsOn C' ·) F.val

theorem subfan_spec (F : Fan C x y)
  (C' : EdgeColoring c G)
  (P : Path C a b x)
  (h : isInverted C C' P)
  (h2 : a ∈ freeColorsOn C (last F)) :
  a ∈ freeColorsOn C' (last (findSubfanWithColor C F C' P h)) := by
  simp [last]
  by_cases hF : (findSubfanWithColor C F C' P h).val = F.val
  simp_rw [hF]


  sorry

  simp [findSubfanWithColor]



  sorry
