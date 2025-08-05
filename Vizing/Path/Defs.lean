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
