import Vizing.EdgeColoring

set_option linter.dupNamespace false
set_option push_neg.use_distrib true

namespace Fan
open Graph
open EdgeColoring
open Aux

variable {n : Nat} {c : Nat} (G : Graph n) (C : EdgeColoring c G)

@[simp]
def fan_prop (x : Vertex n) (f₁ f₂ : Vertex n) :=
  color c G C (x, f₂) ∈ freeColorsOn G C f₁

def colorAx (F : Array (Vertex n)) (x : Vertex n) :=
  F.toList.Chain' (fan_prop G C x)

structure Fan (x y : Vertex n) where
  val : Array (Vertex n)
  nborsAx : val.toList ⊆ (nbhd G x).val
  nonemptyAx : val ≠ #[]
  firstElemAx : val[0]'(by exact Array.size_pos_iff.mpr nonemptyAx) = y
  colorAx : colorAx G C val x
  nodupAx : val.toList.Nodup

variable {n c : Nat} {G : Graph n} {C : EdgeColoring c G} {x y : Vertex n}

theorem fan_colored_edges (x y : Vertex n) (F : Fan G C x y) :
  ∀ u ∈ F.val, u ≠ y → (color c G C (x, u)).isSome := by
  intro u h1 h2
  rw [← Array.mem_toList_iff] at h1
  have := chain'_rel F.colorAx h1
    (List.ne_nil_of_mem h1)
    (by rw [← F.firstElemAx] at h2; exact Ne.symm h2)
  simp [freeColorsOn, allColors] at this
  rcases this with ⟨_, ⟨_, ⟨⟨a, ha⟩, _⟩⟩⟩
  apply Option.isSome_iff_exists.mpr
  use a; exact Eq.symm ha

def last (F : Fan G C x y) :=
  F.val.back (by exact Array.size_pos_iff.mpr F.nonemptyAx)

theorem back_neq (F : Fan G C x y) (h : F.val.size > 1) :
  F.val.back (by exact Array.size_pos_iff.mpr F.nonemptyAx) ≠ y := by
  simp [← F.firstElemAx, Array.back]
  intro hc
  apply (List.Nodup.getElem_inj_iff F.nodupAx).mp at hc
  have := Nat.eq_add_of_sub_eq ?_ hc
  all_goals linarith
