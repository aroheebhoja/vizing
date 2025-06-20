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
  nodupAx : val.toList.Nodup

def default (x y : Vertex n) (h : present n G (x, y)) : Fan n c G C x y where
  val := #[y]
  nborsAx := by
    simp
    exact h.right
  firstElemAx := by congr
  nonemptyAx := by exact Array.ne_empty_of_size_eq_add_one rfl
  colorAx := by simp [colorAx]
  nodupAx := by simp

def add (x y : Vertex n) (F : Array (Vertex n)) (nbors : List (Vertex n))
  (h : F ≠ #[]) :=
  match (List.attach nbors).find? (fun ⟨z, _⟩ ↦
    color n c G C (x, z) ∈ freeColorsOn n c G C (F.back (Array.size_pos_iff.mpr h))) with
  | some z => add x y (F.push z.val) (nbors.erase z.val) Array.push_ne_empty
  | none => F
  termination_by nbors.length
  decreasing_by
    rw [List.length_erase_of_mem z.prop]
    apply Nat.sub_one_lt_of_le
    apply List.length_pos_iff_exists_mem.mpr
    exact ⟨z.val, z.prop⟩
    rfl

theorem add_nborsAx (x y : Vertex n) (F : Array (Vertex n))
  (nbors : List (Vertex n)) (hne : F ≠ #[]) (h : F.toList ⊆ nbhd n G x)
  (hn : nbors ⊆ nbhd n G x) :
  (add n c G C x y F nbors hne).toList ⊆ nbhd n G x := by
  induction F, nbors, hne using add.induct n c G C x
  · rename_i F nbors hne z hz ih
    rw [add]; simp_all
    apply ih
    · exact hn z.prop
    · grw [List.erase_subset]; assumption
  · rename_i nbors _ _ hz
    rw [add, hz]; simp_all

theorem add_nonemptyAx (x y : Vertex n) (F : Array (Vertex n))
  (nbors : List (Vertex n)) (hne : F ≠ #[]) :
  (add n c G C x y F nbors hne) ≠ #[] := by
  induction F, nbors, hne using add.induct n c G C x
  · rw [add]; simp_all
  · rename_i hz
    rw [add, hz]; simp_all

theorem add_firstElemAx (x y : Vertex n) (F : Array (Vertex n))
  (nbors : List (Vertex n)) (hne : F ≠ #[])
  (h : F[0]'(Array.size_pos_iff.mpr hne) = y) :
  (add n c G C x y F nbors hne)[0]'(Array.size_pos_iff.mpr
    (add_nonemptyAx n c G C x y F nbors hne)) = y := by
  induction F, nbors, hne using add.induct n c G C x
  · rename_i F nbors hne z hz ih
    unfold add; simp_all only
    apply ih
    simp_all [Array.getElem_push]
  · unfold add; simp_all only

theorem add_colorAx (x y : Vertex n) (F : Array (Vertex n))
  (nbors : List (Vertex n)) (hne : F ≠ #[]) (h : colorAx n c G C F x) :
  colorAx n c G C (add n c G C x y F nbors hne) x := by
  simp [colorAx]
  induction F, nbors, hne using add.induct n c G C x
  · rename_i F nbors hne z hz ih
    rw [add]; simp_all only
    apply ih
    simp [colorAx] at ⊢ h
    intro i hi
    by_cases hsize : i < F.size - 1
    · have : (F.push z)[i+1]'(by simp [Array.size_push]; linarith) = F[i+1] := by
        apply Array.getElem_push_lt
      simp [Array.getElem_push_lt hi, this]
      exact h i hsize
    · have : i = F.size - 1 := by
        simp at hsize; omega
      subst this
      simp [Nat.sub_add_cancel (Nat.one_le_of_lt hi), Array.getElem_push_lt hi]
      apply List.find?_some at hz; simp [Array.back] at hz
      exact hz
  · rw [add]
    simp_all only [colorAx, implies_true]














#exit

def add_next (x y : Vertex n) (F : Array (Vertex n))
  (nbors : List (Vertex n)) (h : F ≠ #[]) : Array (Vertex n) × List (Vertex n) :=
  match nbors with
  | [] => (F, [])
  | next :: rest =>
    if color n c G C (x, next) ∈ freeColorsOn n c G C
      (F.back (by exact Array.size_pos_iff.mpr h)) then
      ((F.push next), rest) else
    Prod.map id (next :: ·) (add_next x y F rest h)

#exit
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

theorem add_nodupAx (x y : Vertex n) (F : Array (Vertex n))
  (nbors : List (Vertex n)) (hn : nbors.Nodup) (hne : F ≠ #[]) (h : F.toList.Nodup)
  (hdisjoint : List.Disjoint nbors F.toList) :
  (add n c G C x y F nbors hne).toList.Nodup := by
  induction' nbors with z zs ih generalizing F
  <;> simp [add]
  · assumption
  split_ifs; all_goals rename_i h'
  · apply ih
    · exact List.Nodup.of_cons hn
    · simp only [Array.toList_push]
      apply List.nodup_append.mpr
      repeat any_goals apply And.intro
      · assumption
      · exact List.nodup_singleton z
      · exact List.Disjoint.symm
          (List.disjoint_of_disjoint_append_left_left hdisjoint)
    · simp only [Array.toList_push]
      apply List.disjoint_append_right.mpr
      constructor
      · exact List.Disjoint.symm (List.disjoint_of_disjoint_cons_right
        (List.Disjoint.symm hdisjoint))
      · exact List.Disjoint.symm (List.disjoint_of_nodup_append hn)
  · apply ih
    · exact List.Nodup.of_cons hn
    · assumption
    · exact List.Disjoint.symm (List.disjoint_of_disjoint_cons_right
      (List.Disjoint.symm hdisjoint))

theorem add_is_maximal (x y : Vertex n) (F : Array (Vertex n))
  (nbors : List (Vertex n)) (hn : nbors.Nodup) (hne : F ≠ #[]) :
  ¬ ∃ v, ((add n c G C x y F nbors hne).push v).toList.Nodup ∧
    colorAx n c G C ((add n c G C x y F nbors hne).push v) x := by

  sorry


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

theorem mkMaxFan_nodupAx (x y : Vertex n) (hpres : present n G (x, y)) :
  (mkMaxFan n c G C x y hpres).toList.Nodup := by
  simp [mkMaxFan, default]
  apply add_nodupAx
  · apply List.Nodup.erase y
    exact (nbhd n G x).prop.right
  · exact List.nodup_singleton y
  · apply List.disjoint_singleton.mpr
    apply List.Nodup.not_mem_erase
    exact (nbhd n G x).prop.right

def maximalFan (x y : Vertex n) (h : present n G (x, y)) : Fan n c G C x y where
  val := mkMaxFan n c G C x y h
  nborsAx := mkMaxFan_nborsAx n c G C x y h
  firstElemAx := mkMaxFan_firstElemAx n c G C x y h
  nonemptyAx := mkMaxFan_nonemptyAx n c G C x y h
  colorAx := mkMaxFan_colorAx n c G C x y h
  nodupAx := mkMaxFan_nodupAx n c G C x y h

end Fan
