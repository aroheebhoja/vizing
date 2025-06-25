import Vizing.EdgeColoring

set_option linter.dupNamespace false
set_option push_neg.use_distrib true

namespace Fan
open Graph
open EdgeColoring
open Aux

/-

A fan on (x, y) is a nonempty distinct list of vertices
that are all adjacent to x such that
the color of (x, F[i]) is free on F[i+1].

Definition/axioms for a fan, and implementation of a function that creates
a maximal fan from an edge (x, y).

(Proof of maximality will happen once I define the notion of a subfan!)

-/

variable {n : Nat} {c : Nat} (G : Graph n) (C : EdgeColoring c G)

def colorAx (F : Array (Vertex n)) (x : Vertex n) :=
  ∀ i, (h : i < (F.size - 1)) →
  (color c G C (x, F[i + 1]'(by exact Nat.add_lt_of_lt_sub h))) ∈
  (freeColorsOn G C F[i])

structure Fan (x y : Vertex n) where
  val : Array (Vertex n)
  nborsAx : val.toList ⊆ (nbhd G x).val
  nonemptyAx : val ≠ #[]
  firstElemAx : val[0]'(by exact Array.size_pos_iff.mpr nonemptyAx) = y
  colorAx : colorAx G C val x
  nodupAx : val.toList.Nodup

def default (x y : Vertex n) (h : present G (x, y)) : Fan G C x y where
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
    color c G C (x, z) ∈ freeColorsOn G C (F.back (Array.size_pos_iff.mpr h))) with
  | some z => add x y (F.push z.val) (nbors.erase z.val) Array.push_ne_empty
  | none => F
  termination_by nbors.length
  decreasing_by
    rw [List.length_erase_of_mem z.prop]
    apply Nat.sub_one_lt_of_le
    apply List.length_pos_iff_exists_mem.mpr
    exact ⟨z.val, z.prop⟩
    rfl

#check add.induct

theorem add_nborsAx (x y : Vertex n) (F : Array (Vertex n))
  (nbors : List (Vertex n)) (hne : F ≠ #[]) (h : F.toList ⊆ (nbhd G x).val)
  (hn : nbors ⊆ (nbhd G x).val) :
  (add G C x y F nbors hne).toList ⊆ (nbhd G x).val := by
  fun_induction add G C x y F nbors hne
  · rename_i F nbors hne z hz ih
    simp_all
    apply ih
    · exact hn z.prop
    · grw [List.erase_subset]; assumption
  · simp_all

theorem add_nonemptyAx (x y : Vertex n) (F : Array (Vertex n))
  (nbors : List (Vertex n)) (hne : F ≠ #[]) :
  (add G C x y F nbors hne) ≠ #[] := by
  fun_induction add G C x y F nbors hne <;> simp_all

theorem add_preserves_mem (x y : Vertex n) (F : Array (Vertex n))
  (nbors : List (Vertex n)) (hne : F ≠ #[]) :
  ∀ a, a ∈ F → a ∈ add G C x y F nbors hne := by
  intro a ha
  fun_induction add G C x y F nbors hne <;> simp_all

theorem add_maximal (x y : Vertex n) (F : Array (Vertex n))
  (nbors : List (Vertex n)) (hne : F ≠ #[]) :
  ∀ z ∈ nbors, z ∉ (add G C x y F nbors hne) →
    color c G C (x, z) ∉ (freeColorsOn G C
    ((add G C x y F nbors hne).back (Array.size_pos_iff.mpr
      (add_nonemptyAx G C x y F nbors hne)))) := by
  fun_induction add G C x y F nbors hne
  · rename_i F nbors hne z hz ih
    unfold add
    simp_all
    intro w hw1 hw2
    apply ih
    rw [List.mem_erase_of_ne]
    any_goals assumption
    contrapose! hw2
    subst hw2
    exact add_preserves_mem G C x y (F.push z) (nbors.erase z)
      Array.push_ne_empty z.val Array.mem_push_self
  · rename_i nbors hne h
    unfold add
    simp_rw [h]
    simp at h
    intro w hw1 hw2
    exact h w hw1

theorem add_firstElemAx (x y : Vertex n) (F : Array (Vertex n))
  (nbors : List (Vertex n)) (hne : F ≠ #[])
  (h : F[0]'(Array.size_pos_iff.mpr hne) = y) :
  (add G C x y F nbors hne)[0]'(Array.size_pos_iff.mpr
    (add_nonemptyAx G C x y F nbors hne)) = y := by
  fun_induction add G C x y F nbors hne
  · rename_i F nbors hne z hz ih
    unfold add; simp_all only
    apply ih
    simp_all [Array.getElem_push]
  · unfold add; simp_all only

theorem add_colorAx (x y : Vertex n) (F : Array (Vertex n))
  (nbors : List (Vertex n)) (hne : F ≠ #[]) (h : colorAx G C F x) :
  colorAx G C (add G C x y F nbors hne) x := by
  simp [colorAx]
  fun_induction add G C x y F nbors hne
  · rename_i F nbors hne z hz ih
    simp_all only
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
  · simp_all only [colorAx, implies_true]

theorem add_nodupAx (x y : Vertex n) (F : Array (Vertex n))
  (nbors : List (Vertex n)) (hn : nbors.Nodup) (hne : F ≠ #[]) (h : F.toList.Nodup)
  (hdisjoint : List.Disjoint nbors F.toList) :
  (add G C x y F nbors hne).toList.Nodup := by
  fun_induction add G C x y F nbors hne
  · rename_i F nbors hne z hz ih
    simp_all only
    apply ih
    · exact List.Nodup.erase z.val hn
    · simp
      apply List.nodup_append.mpr
      use h, List.nodup_singleton z.val
      specialize hdisjoint z.prop
      simp_all
    · simp [List.Disjoint] at hdisjoint ⊢
      intro a h
      constructor
      · apply hdisjoint
        exact List.mem_of_mem_erase h
      · by_contra ha
        subst ha
        exact List.Nodup.not_mem_erase hn h
  · simp_all only

def mkMaxFan (x y : Vertex n) (h : present G (x, y)) : Array (Vertex n) :=
  add G C x y (default G C x y h).val
  ((nbhd G x).val.erase y) (default G C x y h).nonemptyAx

variable (x y : Vertex n)

theorem mkMaxFan_nborsAx (hpres : present G (x, y)) :
  (mkMaxFan G C x y hpres).toList ⊆ (nbhd G x).val := by
  simp [mkMaxFan, default]
  simp [present] at hpres
  apply add_nborsAx
  · simp
    exact hpres.right
  · exact List.erase_subset

theorem mkMaxFan_nonemptyAx (x y : Vertex n) (hpres : present G (x, y)) :
  mkMaxFan G C x y hpres ≠ #[] := by
  simp [mkMaxFan, default, add_nonemptyAx]

theorem mkMaxFan_firstElemAx (x y : Vertex n) (hpres : present G (x, y)) :
  (mkMaxFan G C x y hpres)[0]'(by
  exact Array.size_pos_iff.mpr (mkMaxFan_nonemptyAx G C x y hpres))
  = y := by
  simp [mkMaxFan, default, add_firstElemAx]

theorem mkMaxFan_colorAx (x y : Vertex n) (hpres : present G (x, y)) :
  colorAx G C (mkMaxFan G C x y hpres) x := by
  simp [mkMaxFan, (default G C x y hpres).colorAx, add_colorAx]

theorem mkMaxFan_nodupAx (x y : Vertex n) (hpres : present G (x, y)) :
  (mkMaxFan G C x y hpres).toList.Nodup := by
  simp [mkMaxFan, default]
  apply add_nodupAx
  · apply List.Nodup.erase y
    exact (nbhd G x).prop.right
  · exact List.nodup_singleton y
  · apply List.disjoint_singleton.mpr
    apply List.Nodup.not_mem_erase
    exact (nbhd G x).prop.right

theorem mkMaxFan_maximal (x y : Vertex n) (hpres : present G (x, y)) :
  ∀ z ∈ ((nbhd G x).val.erase y), z ∉ mkMaxFan G C x y hpres →
    color c G C (x, z) ∉ (freeColorsOn G C
    ((mkMaxFan G C x y hpres).back (Array.size_pos_iff.mpr
      (mkMaxFan_nonemptyAx G C x y hpres)))) := by
  simp [mkMaxFan, default]
  apply add_maximal

def maximalFan (x y : Vertex n) (h : present G (x, y)) : Fan G C x y where
  val := mkMaxFan G C x y h
  nborsAx := mkMaxFan_nborsAx G C x y h
  firstElemAx := mkMaxFan_firstElemAx G C x y h
  nonemptyAx := mkMaxFan_nonemptyAx G C x y h
  colorAx := mkMaxFan_colorAx G C x y h
  nodupAx := mkMaxFan_nodupAx G C x y h

end Fan
