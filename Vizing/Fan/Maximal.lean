import Vizing.EdgeColoring
import Vizing.Fan.Defs

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

variable {n c : Nat} {G : Graph n} (C : EdgeColoring c G)

def singletonFan {x y : Vertex n} (h : present G (x, y)) : Fan C x y where
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
    color C (x, z) ∈ freeColorsOn C (F.back (Array.size_pos_iff.mpr h))) with
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
  (nbors : List (Vertex n)) (hne : F ≠ #[]) (h : F.toList ⊆ (nbhd G x).val)
  (hn : nbors ⊆ (nbhd G x).val) :
  (add C x y F nbors hne).toList ⊆ (nbhd G x).val := by
  fun_induction add C x y F nbors hne
  · rename_i F nbors hne z hz ih
    simp_all
    apply ih
    · exact hn z.prop
    · grw [List.erase_subset]; assumption
  · simp_all

theorem add_nonemptyAx (x y : Vertex n) (F : Array (Vertex n))
  (nbors : List (Vertex n)) (hne : F ≠ #[]) :
  (add C x y F nbors hne) ≠ #[] := by
  fun_induction add C x y F nbors hne <;> simp_all

theorem add_preserves_mem (x y : Vertex n) (F : Array (Vertex n))
  (nbors : List (Vertex n)) (hne : F ≠ #[]) :
  ∀ a, a ∈ F → a ∈ add C x y F nbors hne := by
  intro a ha
  fun_induction add C x y F nbors hne <;> simp_all

theorem add_maximal (x y : Vertex n) (F : Array (Vertex n))
  (nbors : List (Vertex n)) (hne : F ≠ #[]) :
  ∀ z ∈ nbors, z ∉ (add C x y F nbors hne) →
    color C (x, z) ∉ (freeColorsOn C
    ((add C x y F nbors hne).back (Array.size_pos_iff.mpr
      (add_nonemptyAx C x y F nbors hne)))) := by
  fun_induction add C x y F nbors hne
  · rename_i F nbors hne z hz ih
    unfold add
    simp_all
    intro w hw1 hw2
    apply ih
    rw [List.mem_erase_of_ne]
    any_goals assumption
    contrapose! hw2
    subst hw2
    exact add_preserves_mem C x y (F.push z) (nbors.erase z)
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
  (add C x y F nbors hne)[0]'(Array.size_pos_iff.mpr
    (add_nonemptyAx C x y F nbors hne)) = y := by
  fun_induction add C x y F nbors hne
  · rename_i F nbors hne z hz ih
    unfold add; simp_all only
    apply ih
    simp_all [Array.getElem_push]
  · unfold add; simp_all only

theorem add_colorAx (x y : Vertex n) (F : Array (Vertex n))
  (nbors : List (Vertex n)) (hne : F ≠ #[]) (h : colorAx C F x) :
  colorAx C (add C x y F nbors hne) x := by
  fun_induction add C x y F nbors hne
  · rename_i F nbors hne z hz ih
    simp_all only
    apply ih
    simp [colorAx] at ⊢ h
    apply List.Chain'.append
    · exact h
    · apply List.chain'_singleton
    · simp_all
      intro w h
      apply List.find?_some at hz
      simp at hz
      rcases back_of_back? h with ⟨_, h⟩
      rwa [h] at hz
  · simp_all [colorAx]

theorem add_nodupAx (x y : Vertex n) (F : Array (Vertex n))
  (nbors : List (Vertex n)) (hn : nbors.Nodup) (hne : F ≠ #[]) (h : F.toList.Nodup)
  (hdisjoint : List.Disjoint nbors F.toList) :
  (add C x y F nbors hne).toList.Nodup := by
  fun_induction add C x y F nbors hne
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

variable {x y : Vertex n}

def mkMaxFan {x y : Vertex n} (h : present G (x, y)) : Array (Vertex n) :=
  add C x y (singletonFan C h).val
  ((nbhd G x).val.erase y) (singletonFan C h).nonemptyAx

theorem mkMaxFan_nonemptyAx (hpres : present G (x, y)) :
  mkMaxFan C hpres ≠ #[] := by
  simp [mkMaxFan, singletonFan, add_nonemptyAx]

theorem mkMaxFan_maximal (hpres : present G (x, y)) :
  ∀ z ∈ ((nbhd G x).val.erase y), z ∉ mkMaxFan C hpres →
    color C (x, z) ∉ (freeColorsOn C
    ((mkMaxFan C hpres).back (Array.size_pos_iff.mpr
      (mkMaxFan_nonemptyAx C hpres)))) := by
  simp [mkMaxFan, singletonFan]
  apply add_maximal

def maximalFan {x y : Vertex n} (h : present G (x, y)) : Fan C x y where
  val := mkMaxFan C h
  nborsAx := by
    simp [mkMaxFan, singletonFan]
    simp [present] at h
    apply add_nborsAx
    · simp
      exact h.right
    · exact List.erase_subset
  nonemptyAx := mkMaxFan_nonemptyAx C h
  firstElemAx := by simp [mkMaxFan, singletonFan, add_firstElemAx]
  colorAx := by simp [mkMaxFan, (singletonFan C h).colorAx, add_colorAx]
  nodupAx := by
    simp [mkMaxFan, singletonFan]
    apply add_nodupAx
    · apply List.Nodup.erase y
      exact (nbhd G x).nodupAx
    · exact List.nodup_singleton y
    · apply List.disjoint_singleton.mpr
      apply List.Nodup.not_mem_erase
      exact (nbhd G x).nodupAx

end Fan
