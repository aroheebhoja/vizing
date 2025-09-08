import Vizing.Path.Extend

namespace Path
open Graph
open EdgeColoring
open Aux

variable {n c : Nat} {G : Graph n} (C : EdgeColoring c G)

structure Path (a b : Color c) (x : Vertex n) where
  val : List (Vertex n)
  nonemptyAx : val ≠ []
  firstElemAx : val[0]'(by exact List.length_pos_iff.mpr nonemptyAx) = x
  nodupAx : val.Nodup
  colorAx : alternatesColor C val a b

variable {a b : Color c} {x : Vertex n}
  (ha : a.isSome)
  (hb : b.isSome)
  (hne : a ≠ b)
  (hfree : b ∈ freeColorsOn C x)

def singletonPath : Path C a b x where
  val := [x]
  nonemptyAx := by simp
  firstElemAx := by simp
  nodupAx := List.nodup_singleton x
  colorAx := by
    rw [alternatesColor, alternates]
    trivial

def mkMaxPath : List (Vertex n) :=
  let P := singletonPath C
  extendPath C P.val P.nonemptyAx P.firstElemAx hfree P.nodupAx ha hb hne P.colorAx

def maximalPath : Path C a b x where
  val := mkMaxPath C ha hb hne hfree
  nonemptyAx := by simp [mkMaxPath, singletonPath, extendPath_nonemptyAx]
  firstElemAx := by simp [mkMaxPath, singletonPath, extendPath_firstElemAx]
  nodupAx := by simp [mkMaxPath, singletonPath, extendPath_nodupAx]
  colorAx := by simp [mkMaxPath, singletonPath, extendPath_colorAx]

/-
TODO: State and prove maximality

Maximal path is maximal: if last edge is colored a,
then b is free on last vertex, and vice versa
-/

def isMaximalPath {C : EdgeColoring c G} (P : Path C a b x) :=
  next a b P.val ∈ freeColorsOn C (P.val.getLast P.nonemptyAx)

theorem maximalPath_isMaximal :
  isMaximalPath (maximalPath C ha hb hne hfree) := by
  simp [maximalPath, mkMaxPath]
  apply extendPath_maximal

theorem isLast_if {P : Path C a b x} {u : Vertex n}
  (h1 : u ∈ P.val) (h2 : a ∈ freeColorsOn C u) :
  u = P.val[P.val.length - 1]'(by
    apply Nat.sub_one_lt;
    apply Nat.ne_zero_iff_zero_lt.mpr;
    exact List.length_pos_of_mem h1) := by
  rcases List.getElem_of_mem h1 with ⟨i, h, hi⟩
  simp_rw [← hi]
  apply (List.Nodup.getElem_inj_iff P.nodupAx).mpr
  by_contra
  have : i = 0 ∨ (0 < i ∧ i < P.val.length - 1) := by omega
  have hcolor := P.colorAx
  rcases this with hi | hi
  · subst hi
    rw [alternatesColor, alternates.eq_def] at hcolor
    split at hcolor <;> simp_all
    rcases hcolor with ⟨hcolor, _⟩
    apply not_exists_of_freeColor at h2
    simp_all
  · rw [alternatesColor] at hcolor
    apply middle_spec at hcolor
    specialize hcolor i hi
    apply not_exists_of_freeColor at h2
    simp_all [color_symm]
