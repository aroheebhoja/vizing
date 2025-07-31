import Vizing.Path.AlternatingPred

set_option linter.dupNamespace false
set_option push_neg.use_distrib true
set_option maxHeartbeats 10000000

namespace Path
open Graph
open EdgeColoring
open Aux

variable {c n : Nat} {G : Graph n} (C : EdgeColoring c G)
  (P : List (Vertex n)) (a b : Color c) (hne : P ≠ [])
  (x : Vertex n)
  (hx : P[0]'(by exact List.length_pos_iff.mpr hne) = x)
  (hfree : b ∈ freeColorsOn C x)
  (hnodup : P.Nodup)

def alternatesColor :=
  alternates (fun v₁ v₂ ↦ color C (v₁, v₂)) a b P

def nextVertex :=
  findNborWithColor C (P.getLast hne) (next a b P)

include hx hfree in
theorem nextVertex_not_mem
  (hnodup : P.Nodup)

  (h : (nextVertex C P a b hne).isSome) :
  (nextVertex C P a b hne).get h ∉ P := by
  intro hc
  rcases Option.isSome_iff_exists.mp h with ⟨z, hz1⟩
  simp only [hz1, Option.get_some] at hc
  unfold nextVertex findNborWithColor at hz1
  apply List.find?_some at hz1
  simp at hz1
  rcases List.getElem_of_mem hc with ⟨i, _, hz2⟩
  have : i = 0 ∨ 0 < i ∧ i < P.length - 1 ∨ i = P.length - 1 := by
    omega
  rcases this with hi | hi | hi
    -- Case 1: z is the first element
  · subst hi
    rcases next_eq_a_or_b a b P with hnext | hnext
    · sorry
    · rw [hnext, color_symm] at hz1
      subst hz2; subst hx
      apply not_exists_of_freeColor at hfree
      simp_all
    -- Case 2: z is a middle element
  ·
    sorry
    -- Case 3: z is the last element
  · sorry

  -- rcases next_eq_a_or_b a b P with hnext | hnext
  -- -- Next color is a
  -- rw [hnext] at hz1
  -- sorry


  -- -- Next color is b
  -- sorry

def extendPath (a b : Color c) (P : List (Vertex n)) (hne : P ≠ [])
  (hnodup : P.Nodup) (hcolor : alternatesColor C P a b) : List (Vertex n) :=
  match Option.attach (nextVertex C P a b hne) with
  | none => P
  | some ⟨z, h⟩ =>
    have hnodup' : (P.concat z).Nodup := by
      apply List.Nodup.concat ?_ hnodup
      stop
      have := nextVertex_not_mem C P a b hne hnodup (by exact Option.isSome_of_mem h)
      simp_all only [Option.get_some, not_false_eq_true]
    have hcolor' : alternatesColor C (P.concat z) a b := by
      rw [alternatesColor]
      apply alternates_concat z hne hcolor
      induction' P with head tail ih generalizing a b
      · contradiction
      · rw [nextVertex, next, findNborWithColor] at h
        apply List.find?_some at h
        simp at h
        rwa [next]
    extendPath a b (P.concat z) (by simp) hnodup' hcolor'
  termination_by (n + 1) - P.length
  decreasing_by
    simp only [List.concat_eq_append, List.length_append,
      List.length_cons, List.length_nil, zero_add]
    apply Nat.sub_succ_lt_self
    grw [List.Nodup.length_le_card hnodup]
    simp
