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
  (ha : a.isSome)
  (hb : b.isSome)
  (hneq : a ≠ b)


def alternatesColor :=
  alternates (fun v₁ v₂ ↦ color C (v₁, v₂)) a b P

def nextVertex :=
  findNborWithColor C (P.getLast hne) (next a b P)

def lastColor_eq_b_of_nextColor_eq_a :=
  last_b_of_next_a (fun v₁ v₂ ↦ color C (v₁, v₂)) a b P hne

def lastColor_eq_a_of_nextColor_eq_b :=
  last_a_of_next_b (fun v₁ v₂ ↦ color C (v₁, v₂)) a b P hne

include hx hfree ha hb hneq in
theorem nextVertex_not_mem
  (hnodup : P.Nodup)
  (h : (nextVertex C P a b hne).isSome) (hcolor : alternatesColor C P a b) :
  (nextVertex C P a b hne).get h ∉ P := by
  intro hc
  rcases Option.isSome_iff_exists.mp h with ⟨z, hz1⟩
  simp only [hz1, Option.get_some] at hc
  unfold nextVertex findNborWithColor at hz1
  apply List.find?_some at hz1
  simp at hz1
  rcases List.getElem_of_mem hc with ⟨i, _, hz2⟩
  subst hz2
  have : i = 0 ∨ 0 < i ∧ i < P.length - 1 ∨ i = P.length - 1 := by
    omega
  rcases this with hi | hi | hi
    -- Case 1: z is the first element
  · subst hi
    rcases next_eq_a_or_b a b P with hnext | hnext
    · rw [hnext] at hz1
      rw [alternatesColor, alternates.eq_def] at hcolor
      split at hcolor
      · contradiction
      · rename_i head hlen
        simp at hz1
        rw [self_loop_uncolored C head] at hz1
        apply Option.ne_none_iff_isSome.mpr at ha
        exact ha (Eq.symm hz1)
      · rename_i v₁ v₂ vs hlen
        simp_all
        rw [color_symm] at hz1
        rw [← hcolor.left] at hz1
        rcases color_unique C _ _ _ hz1 with this | this <;> simp_all
        have hvs : vs ≠ [] := by
          by_contra hc
          subst hc
          repeat rw [next] at hnext
          exact hneq (Eq.symm hnext)
        rw [List.getLast_cons hvs] at this
        apply List.getLast_mem at hvs
        simp_all
    · rw [hnext, color_symm] at hz1
      subst hx
      apply not_exists_of_freeColor at hfree
      simp_all
    -- Case 2: z is a middle element
  · rw [alternatesColor] at hcolor
    rcases next_eq_a_or_b a b P with hnext | hnext <;> rw [hnext] at hz1
    · rcases middle_spec hcolor i hi with ⟨hc, _⟩ | ⟨_, hc⟩
      · rw [← hz1, color_symm] at ha
        rw [← hc, color_symm _ _ P[i], color_symm _ _ P[i]] at hz1
        rcases color_unique C _ _ _ hz1 with this | this <;> simp_all
        rw [List.getLast_eq_getElem, List.Nodup.getElem_inj_iff hnodup] at this
        omega
      · rw [← hz1, color_symm] at ha
        rw [← hc, color_symm] at hz1
        rcases color_unique C _ _ _ hz1 with this | this <;> simp_all
        rw [List.getLast_eq_getElem, List.Nodup.getElem_inj_iff hnodup] at this
        have := lastColor_eq_b_of_nextColor_eq_a C P a b hne hnext
        simp_all! +arith
    · rcases middle_spec hcolor i hi with ⟨_, hc⟩ | ⟨hc, _⟩
      · rw [← hz1, color_symm] at hb
        rw [← hc, color_symm] at hz1
        rcases color_unique C _ _ _ hz1 with this | this <;> simp_all
        rw [List.getLast_eq_getElem, List.Nodup.getElem_inj_iff hnodup] at this
        have := lastColor_eq_a_of_nextColor_eq_b C P a b hne hnext
        simp_all! +arith
      · rw [← hz1, color_symm] at hb
        rw [← hc, color_symm _ _ P[i], color_symm _ _ P[i]] at hz1
        rcases color_unique C _ _ _ hz1 with this | this <;> simp_all
        rw [List.getLast_eq_getElem, List.Nodup.getElem_inj_iff hnodup] at this
        omega
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
