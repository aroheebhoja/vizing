import Vizing.Path.AlternatingPred

set_option linter.dupNamespace false
set_option push_neg.use_distrib true
set_option maxHeartbeats 10000000

namespace Path
open Graph
open EdgeColoring
open Aux

variable {c n : Nat} {G : Graph n} (C : EdgeColoring c G)

section
variable
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
  last_b_of_next_a (fun v₁ v₂ ↦ color C (v₁, v₂)) a b P

def lastColor_eq_a_of_nextColor_eq_b :=
  last_a_of_next_b (fun v₁ v₂ ↦ color C (v₁, v₂)) a b P

include hx hfree ha hb hneq hnodup in
theorem nextVertex_not_mem
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
    have hlen : P.length > 1 := by omega

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
        have := lastColor_eq_b_of_nextColor_eq_a C P a b hlen hcolor hnext
        simp_all
    · rcases middle_spec hcolor i hi with ⟨_, hc⟩ | ⟨hc, _⟩
      · rw [← hz1, color_symm] at hb
        rw [← hc, color_symm] at hz1
        rcases color_unique C _ _ _ hz1 with this | this <;> simp_all
        rw [List.getLast_eq_getElem, List.Nodup.getElem_inj_iff hnodup] at this
        have := lastColor_eq_a_of_nextColor_eq_b C P a b hlen hcolor hnext
        simp_all
      · rw [← hz1, color_symm] at hb
        rw [← hc, color_symm _ _ P[i], color_symm _ _ P[i]] at hz1
        rcases color_unique C _ _ _ hz1 with this | this <;> simp_all
        rw [List.getLast_eq_getElem, List.Nodup.getElem_inj_iff hnodup] at this
        omega
    -- Case 3: z is the last element
  · have : (next a b P).isSome := by
      rcases next_eq_a_or_b a b P with hnext | hnext <;> rwa [hnext]
    simp_rw [← hz1, hi, List.getLast_eq_getElem, self_loop_uncolored] at this
    simp at this
end

def extendPath {a b : Color c} {x : Vertex n}
  (P : List (Vertex n)) (hne : P ≠ [])
  (hx : P[0]'(by exact List.length_pos_iff.mpr hne) = x)
  (hfree : b ∈ freeColorsOn C x)
  (hnodup : P.Nodup)
  (ha : a.isSome) (hb : b.isSome) (hneq : a ≠ b)
  (hcolor : alternatesColor C P a b) : List (Vertex n) :=
  match Option.attach (nextVertex C P a b hne) with
  | none => P
  | some ⟨z, h⟩ =>
    have hnodup' : (P.concat z).Nodup := by
      apply List.Nodup.concat ?_ hnodup
      have := nextVertex_not_mem C P a b hne x hx hfree hnodup ha hb hneq
        (by exact Option.isSome_of_mem h) hcolor
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
    have hx' : (P.concat z)[0]'(by simp) = x := by
      simp_rw [← hx, List.concat_eq_append, List.getElem_append]
      split
      · rfl
      · rename_i hc; simp at hc; contradiction
    extendPath (P.concat z) (by simp) hx' hfree hnodup' ha hb hneq hcolor'
  termination_by (n + 1) - P.length
  decreasing_by
    simp only [List.concat_eq_append, List.length_append,
      List.length_cons, List.length_nil, zero_add]
    apply Nat.sub_succ_lt_self
    grw [List.Nodup.length_le_card hnodup]
    simp

#check extendPath

variable
  (P : List (Vertex n))
  {a b : Color c}
  {x : Vertex n}
  (hne : P ≠ [])
  (hx : P[0]'(by exact List.length_pos_iff.mpr hne) = x)
  (hfree : b ∈ freeColorsOn C x)
  (hnodup : P.Nodup)
  (ha : a.isSome)
  (hb : b.isSome)
  (hneq : a ≠ b)
  (hcolor : alternatesColor C P a b)

theorem extendPath_nonemptyAx :
  extendPath C P hne hx hfree hnodup ha hb hneq hcolor ≠ [] := by
  fun_induction extendPath C P hne hx hfree hnodup ha hb hneq hcolor <;> simp_all

theorem extendPath_firstElemAx :
  (extendPath C P hne hx hfree hnodup ha hb hneq hcolor)[0]'(by
    apply List.length_pos_iff.mpr;
    exact extendPath_nonemptyAx C P hne hx hfree hnodup ha hb hneq hcolor) = x := by
    fun_induction extendPath C P hne hx hfree hnodup ha hb hneq hcolor <;> unfold extendPath
    · rename_i h
      simp_rw [h]
      assumption
    · rename_i h _ _ _ ih
      simp_rw [h]
      assumption

theorem extendPath_nodupAx :
  (extendPath C P hne hx hfree hnodup ha hb hneq hcolor).Nodup := by
  fun_induction extendPath C P hne hx hfree hnodup ha hb hneq hcolor <;> simp_all

theorem extendPath_colorAx :
  alternatesColor C (extendPath C P hne hx hfree hnodup ha hb hneq hcolor) a b := by
  fun_induction extendPath C P hne hx hfree hnodup ha hb hneq hcolor <;> simp_all
