import Vizing.Fan
import Vizing.Pop

namespace Fan
open Graph
open EdgeColoring
open Aux

variable
  {n c : Nat} (G : Graph n) (C : EdgeColoring c G) (x y : Vertex n)
  (F : Fan G C x y)


/-
Given a fan F[1:k] of a vertex X, the "rotate fan" operation does the
following: for i = 1, ..., k–1, assign the color of (X,F[i + 1]) to
edge (X,F[i]). Finally, uncolor (X, F[k]).

This operation leaves the coloring valid because, by the definition of
a fan, the color of (X,F[i+1]) was free on F[i].
-/

def removeLast (F : Fan G C x y) (h : F.val.size > 1) : Fan G C x y where
  val := F.val.pop
  nborsAx := by
    intro u h
    apply F.nborsAx
    exact List.mem_of_mem_dropLast h
  nonemptyAx := by
    apply Array.size_pos_iff.mp
    simpa
  firstElemAx := by
    simp
    exact F.firstElemAx
  colorAx := by
    simp [colorAx]
    intro i h
    exact F.colorAx i (by exact Nat.lt_of_lt_pred h)
  nodupAx := by
    apply dropLast_nodup_of_nodup
    exact F.nodupAx

theorem back_neq (F : Fan G C x y) (h : F.val.size > 1) :
  F.val.back (by exact Array.size_pos_iff.mpr F.nonemptyAx) ≠ y := by
  simp [← F.firstElemAx, Array.back]
  intro hc
  have := @List.Nodup.getElem_inj_iff _ F.val.toList
    F.nodupAx 0 (by simp; exact Array.size_pos_iff.mpr F.nonemptyAx)
    (F.val.size - 1) (by simp; linarith)
  simp [Array.getElem_toList] at this
  have := this.mp (Eq.symm hc)
  apply Nat.one_lt_iff_ne_zero_and_ne_one.mp at h
  contrapose! h
  intro x
  rw [← add_zero 1, this]
  apply Eq.symm (Nat.add_sub_of_le ?_)
  linarith

theorem last_present (F : Fan G C x y) :
  present G (x, (last F)) := by
  simp_rw [present, present_symm G (x, last F), and_self, last]
  apply F.nborsAx
  simp

theorem not_in_fan (F : Fan G C x y) : x ∉ F.val := by
  intro h
  have h1 := F.nborsAx h.val
  have h2 := G.noSelfLoopsAx x
  simp [nbhd] at h1
  contradiction

def mkFan (F : Fan G C x y) (a : Color c)
  (hvalid : edgeColorValid G C (x, last F) a) (hsize : F.val.size > 1):
  Fan G (setEdgeColor G C (x, last F) a (last_present G C x y F) hvalid) x y where
  val := popElem F.val F.nonemptyAx
  nborsAx := by
    simp
    intro u h
    apply F.nborsAx
    exact List.mem_of_mem_dropLast h
  nonemptyAx := by
    simp
    apply Array.size_pos_iff.mp
    simpa
  firstElemAx := by
    simp
    exact F.firstElemAx
  nodupAx := by
    simp
    apply dropLast_nodup_of_nodup
    exact F.nodupAx
  colorAx := by
    simp [colorAx]
    intro i h
    have aux1 := freeColors_invariant G C (x, last F) a (last_present G C x y F) hvalid
    have aux2 := color_invariant G C (x, last F) a (last_present G C x y F) hvalid
    have := not_in_fan G C x y F
    rw [← aux1, ← aux2]
    · apply F.colorAx
      exact Nat.lt_of_lt_pred h
    · simp [last, Array.back]
      have := @List.Nodup.getElem_inj_iff _ F.val.toList
        F.nodupAx (i + 1) ?_
        (F.val.size - 1) ?_
      repeat rw [Array.getElem_toList] at this
      constructor
      rw [this]
      · apply Nat.ne_of_lt
        exact Nat.add_lt_of_lt_sub h
      · intro hc
        have : x ∈ F.val := by exact Array.mem_of_getElem (Eq.symm hc)
        contradiction
      · apply Nat.add_lt_of_lt_sub
        simp
        exact Nat.lt_of_lt_pred h
      · simp
        exact Nat.zero_lt_of_lt hsize
    simp
    constructor
    · intro h
      have : x ∈ F.val := by exact Array.mem_of_getElem h
      contradiction
    · simp [last, Array.back]
      have := @List.Nodup.getElem_inj_iff _ F.val.toList
        F.nodupAx i ?_ (F.val.size - 1) ?_
      repeat rw [Array.getElem_toList] at this
      rw [this]
      · apply Nat.ne_of_lt
        exact Nat.lt_of_lt_pred h
      · simp
        exact Nat.lt_of_lt_pred (Nat.lt_of_lt_pred h)
      · simp
        exact Nat.zero_lt_of_lt hsize

def rotateFan (C : EdgeColoring c G) (F : Fan G C x y) (a : Color c)
  (hvalid : edgeColorValid G C (x, last F) a)
  : EdgeColoring c G :=
  let a' := color c G C (x, last F)
  let C' := setEdgeColor G C (x, last F) a (last_present G C x y F) hvalid
  if h : F.val.size > 1 then
  let F' := mkFan G C x y F a hvalid h
  have hvalid' : edgeColorValid G C' (x, last F') a' := by
    simp [edgeColorValid, C', a']
    right
    constructor
    · have := setEdgeColor_freeOn G C (x, last F) (last_present G C x y F) a hvalid ?_
      · simp at this
        exact this.left
      · apply (fan_colored_edges G C x y F)
        all_goals simp [last]
        · simp_rw [← F.firstElemAx]
          simp [Array.back]
          have := @List.Nodup.getElem_inj_iff _ F.val.toList
            F.nodupAx (F.val.size - 1) ?_ 0 ?_
          · repeat rw [Array.getElem_toList] at this
            rw [this]
            apply Nat.ne_of_gt
            exact Nat.zero_lt_sub_of_lt h
          any_goals simp; exact Nat.zero_lt_of_lt h
    · have := freeColors_invariant G C (x, last F) a (last_present G C x y F) hvalid
      rw [← this]
      · simp [last, F', mkFan, Array.back]
        have := F.colorAx (F.val.size - 1 - 1)
        simp at this; specialize this h
        have aux : F.val.size - 1 - 1 + 1 = F.val.size - 1 := by
          apply Nat.sub_add_cancel
          exact Nat.le_sub_one_of_lt h
        simp_rw [aux] at this
        exact this
      · constructor
        · simp [last, Array.back]
          have := not_in_fan G C' x y F'
          intro hc
          apply Array.mem_of_getElem at hc
          contradiction
        · simp [F', last, mkFan]
          have := pop_back F.val F.nonemptyAx h F.nodupAx
          simp [popElem] at this
          exact fun x ↦ this (Eq.symm x)
  rotateFan C' F' a' hvalid'
  else C'
  termination_by F.val.size
  decreasing_by
    simp [mkFan]
    exact Array.size_pos_iff.mpr F.nonemptyAx

end Fan
