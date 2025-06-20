import Vizing.new.EdgeColoring

set_option linter.dupNamespace false
set_option push_neg.use_distrib true

namespace Fan
open Graph
open Nbhd
open EdgeColoring

/-

A fan on (x, y) is a nonempty distinct list of vertices
that are all adjacent to x such that
the color of (x, F[i]) is free on F[i+1].

Definition/axioms for a fan, and implementation of a function that creates
a maximal fan from an edge (x, y).

(Proof of maximality will happen once I define the notion of a subfan!)

-/

variable (n : Nat) (c : Nat) (G : Graph n) (C : EdgeColoring n c G)

def colorAx (F : Array (Vertex n)) (x : Vertex n) :=
  ∀ i, (h : i < (F.size - 1)) →
  (color n c G C (x, F[i + 1]'(by exact Nat.add_lt_of_lt_sub h))) ∈
  (freeColorsOn n c G C F[i])

structure Fan (x y : Vertex n) where
  val : Array (Vertex n)
  nborsAx : val.toList ⊆ (nbhd n G x).val
  nonemptyAx : val ≠ #[]
  firstElemAx : val[0]'(by exact Array.size_pos_iff.mpr nonemptyAx) = y
  colorAx : colorAx n c G C val x

def default (x y : Vertex n) (h : present n G (x, y)) : Fan n c G C x y where
  val := #[y]
  nborsAx := by
    simp
    exact h.right
  firstElemAx := by congr
  nonemptyAx := by exact Array.ne_empty_of_size_eq_add_one rfl
  colorAx := by simp [colorAx]

def add (x y : Vertex n) (F : Array (Vertex n))
  (nbors : List (Vertex n)) (h : F ≠ #[]) : Array (Vertex n) :=
  match nbors with
  | [] => F
  | next :: rest =>
    if color n c G C (x, next) ∈ freeColorsOn n c G C
      (F.back (by exact Array.size_pos_iff.mpr h)) then
    add x y (F.push next) rest (by exact Array.push_ne_empty) else
    add x y F rest h

theorem add_nborsAx (x y : Vertex n) (F : Array (Vertex n))
  (nbors : List (Vertex n)) (hne : F ≠ #[]) (h : F.toList ⊆ nbhd n G x)
  (hn : nbors ⊆ nbhd n G x) :
  (add n c G C x y F nbors hne).toList ⊆ nbhd n G x := by
  induction' nbors with z zs ih generalizing F
  <;> simp [add]
  · assumption
  · split_ifs
    all_goals apply List.cons_subset.mp at hn
    · exact ih (F.push z) (by simp_all) (by simp_all) hn.right
    · exact ih F hne h hn.right

theorem add_nonemptyAx (x y : Vertex n) (F : Array (Vertex n))
  (nbors : List (Vertex n)) (h : F ≠ #[]) :
  (add n c G C x y F nbors h) ≠ #[] := by
  induction' nbors with z zs ih generalizing F
  <;> simp [add]
  · assumption
  · split_ifs
    · exact ih (F.push z) (by exact Array.push_ne_empty)
    · exact ih F h

theorem add_firstElemAx (x y : Vertex n) (F : Array (Vertex n))
  (nbors : List (Vertex n)) (hne : F ≠ #[])
  (h : F[0]'(Array.size_pos_iff.mpr hne) = y) :
  (add n c G C x y F nbors hne)[0]'(Array.size_pos_iff.mpr
    (add_nonemptyAx n c G C x y F nbors hne)) = y := by
  induction' nbors with z zs ih generalizing F
  <;> simp [add]
  · assumption
  · split_ifs
    all_goals apply ih
    · rw [← h]
      exact Array.getElem_push_lt (Array.size_pos_iff.mpr hne)
    · assumption

theorem add_colorAx (x y : Vertex n) (F : Array (Vertex n))
  (nbors : List (Vertex n)) (hne : F ≠ #[]) (h : colorAx n c G C F x) :
  colorAx n c G C (add n c G C x y F nbors hne) x := by
  induction' nbors with z zs ih generalizing F
  <;> simp [add]
  exact h
  split; all_goals rename_i h'
  · apply ih (F.push z)
    unfold colorAx at ⊢ h
    simp only [Array.size_push, add_tsub_cancel_right]
    intro i hi
    by_cases hsize : i < F.size - 1
    · have aux1 : (F.push z)[i]'(by simp [Array.size_push]; linarith) = F[i] := by
        exact Array.getElem_push_lt hi
      have aux2 : (F.push z)[i+1]'(by simp [Array.size_push]; linarith) = F[i+1] := by
        apply Array.getElem_push_lt
      simp_rw [aux1, aux2]
      exact h i hsize
    · have hi' : i = F.size - 1 := by
        simp only [not_lt, tsub_le_iff_right] at hsize
        apply Nat.lt_or_eq_of_le at hsize
        rcases hsize with hsize | hsize
        · linarith
        · exact Nat.eq_sub_of_add_eq (Eq.symm hsize)
      have aux1 : (F.push z)[i+1]'(by simp [Array.size_push]; linarith) = z := by
        subst hi'
        simp_rw [Nat.sub_add_cancel (Nat.one_le_of_lt hi)]
        exact Array.getElem_push_eq
      have aux2 : (F.push z)[i]'(by simp [Array.size_push]; linarith) = F.back := by
        simp_rw [Array.getElem_push_lt (by exact hi), hi']
        rfl
      rw [aux1, aux2]
      assumption
  · exact ih F hne h

def mkMaxFan (x y : Vertex n) (h : present n G (x, y)) : Array (Vertex n) :=
  add n c G C x y (default n c G C x y h).val
  ((nbhd n G x).val.erase y) (default n c G C x y h).nonemptyAx

variable (x y : Vertex n)

theorem mkMaxFan_nborsAx (hpres : present n G (x, y)) :
  (mkMaxFan n c G C x y hpres).toList ⊆ (nbhd n G x).val := by
  simp [mkMaxFan, default]
  simp [present] at hpres
  apply add_nborsAx
  · simp
    exact hpres.right
  · exact List.erase_subset

theorem mkMaxFan_nonemptyAx (x y : Vertex n) (hpres : present n G (x, y)) :
  mkMaxFan n c G C x y hpres ≠ #[] := by
  simp [mkMaxFan, default, add_nonemptyAx]

theorem mkMaxFan_firstElemAx (x y : Vertex n) (hpres : present n G (x, y)) :
  (mkMaxFan n c G C x y hpres)[0]'(by
  exact Array.size_pos_iff.mpr (mkMaxFan_nonemptyAx n c G C x y hpres))
  = y := by
  simp [mkMaxFan, default, add_firstElemAx]

theorem mkMaxFan_colorAx (x y : Vertex n) (hpres : present n G (x, y)) :
  colorAx n c G C (mkMaxFan n c G C x y hpres) x := by
  simp [mkMaxFan, (default n c G C x y hpres).colorAx, add_colorAx]

def maximalFan (x y : Vertex n) (h : present n G (x, y)) : Fan n c G C x y where
  val := mkMaxFan n c G C x y h
  nborsAx := mkMaxFan_nborsAx n c G C x y h
  firstElemAx := mkMaxFan_firstElemAx n c G C x y h
  nonemptyAx := mkMaxFan_nonemptyAx n c G C x y h
  colorAx := mkMaxFan_colorAx n c G C x y h

end Fan
