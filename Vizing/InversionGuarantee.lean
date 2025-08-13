import Vizing.Aux
import Vizing.Graph
import Vizing.EdgeColoring
import Vizing.Fan
import Vizing.Path

open Aux Graph EdgeColoring Fan Path

variable
  {n c : Nat} {G : Graph n} (C : EdgeColoring c G)
  {x y : Vertex n} {a b : Color c}

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
  (h : isInverted C C' P):
  a ∈ freeColorsOn C' (last (findSubfanWithColor C F C' P h)) := by
  simp [last]
  simp [findSubfanWithColor]
  


  sorry
