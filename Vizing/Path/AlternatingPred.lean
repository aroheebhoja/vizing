import Vizing.EdgeColoring

namespace Path
open Graph
open EdgeColoring
open Aux

variable {c n : Nat} {G : Graph n} (C : EdgeColoring c G)

/- Auxiliary functions to define a predicate that alternates
   over contiguous values in a list -/

def alternates {V C : Type*} (p : V → V → C) (a b : C) : List V → Prop
  | []               => True
  | _ :: []        => True
  | v₁ :: (v₂ :: vs) => p v₁ v₂ = a ∧ alternates p b a (v₂ :: vs)

def next {V C : Type*} (a b : C) : List V → C
  | []      => b
  | _ :: vs => next b a vs

theorem next_eq_a_or_b {V C : Type*} (a b : C) (L : List V) :
  next a b L = a ∨ next a b L = b := by
  induction' L with head tail ih generalizing a b <;> simp [next]
  specialize ih b a
  tauto

theorem next_a_b_ne_next_b_a {V C : Type*} (a b : C) (L : List V) (h : a ≠ b)
  : next a b L ≠ next b a L := by
  induction' L with head tail ih <;> simp_all [next, Ne.symm]


mutual
theorem last_b_of_next_a {V C : Type*} (p : V → V → C) (a b : C) (L : List V) (hlen : L.length > 1)
  (h : alternates p a b L)
  (hnext : next a b L = a) : p
    (L[L.length - 2]'(by apply Nat.sub_lt <;> omega))
    (L[L.length - 1]'(by apply Nat.sub_lt <;> omega)) = b := by
    fun_cases alternates
    any_goals contradiction
    rename_i v₁ v₂ vs
    rw [next] at hnext
    by_cases hvs : vs = []
    · subst hvs
      simp_all!
    · apply @last_a_of_next_b _ _ p _ _ _ (by simp; exact List.length_pos_iff.mpr hvs) at hnext
      simp_rw [List.getElem_cons] at ⊢ hnext
      · simp_all! +arith
      · rw [alternates] at h
        exact h.right

theorem last_a_of_next_b {V C : Type*} (p : V → V → C) (a b : C) (L : List V) (hlen : L.length > 1)
  (h : alternates p a b L)
  (hnext : next a b L = b) : p
    (L[L.length - 2]'(by apply Nat.sub_lt <;> omega))
    (L[L.length - 1]'(by apply Nat.sub_lt <;> omega)) = a := by
    fun_cases alternates
    any_goals contradiction
    rename_i v₁ v₂ vs
    rw [next] at hnext
    by_cases hvs : vs = []
    subst hvs
    simp_all!
    apply @last_b_of_next_a _ _ p _ _ _ (by simp; exact List.length_pos_iff.mpr hvs) at hnext
    simp_rw [List.getElem_cons] at ⊢ hnext
    · simp_all! +arith
    · rw [alternates] at h
      exact h.right
end

theorem alternates_concat {V C : Type*} {p : V → V → C} {a b : C} {L : List V} (w : V)
    (Lne : L ≠ [])
    (h : alternates p a b L)
    (h' : p (L.getLast Lne) w = next a b L) :
    alternates p a b (L.concat w) := by
  fun_induction alternates p a b L
  . contradiction
  . trivial
  rename_i a b v₁ v₂ vs ih
  rw [alternates.eq_def]; simp
  use h.left
  rw [← List.concat_eq_append]
  apply ih _ h.right h'

theorem alternates_tail {V C : Type*} {p : V → V → C} {a b : C} {x : V} {xs : List V}
    (h : alternates p a b (x :: xs)) :
    alternates p b a xs := by
    rw [alternates.eq_def] at h
    split at h <;> rename_i heq
    · contradiction
    · simp only [List.cons.injEq] at heq
      rcases heq with ⟨_, h⟩
      subst xs
      trivial
    · simp only [List.cons.injEq] at heq
      rcases heq with ⟨_, h⟩
      subst xs
      exact h.right

theorem alternates_head {V C : Type*} {p : V → V → C} {a b : C} {x : V} {xs : List V}
    (h : alternates p a b (x :: xs)) (h2 : xs.length > 0) :
    p x xs[0] = a := by
    unfold alternates at h
    split at h <;> rename_i heq
    · contradiction
    · simp at heq
      rcases heq with ⟨_, hc⟩
      have : xs.length = 0 := by exact List.eq_nil_iff_length_eq_zero.mp hc
      linarith
    · simp_all

theorem middle_spec {V C : Type*} {p : V → V → C} {a b : C} {L : List V}
  (h : alternates p a b L)
  (i : Nat) (hi : 0 < i ∧ i < L.length - 1) :
  p L[i-1] L[i] = a ∧ p L[i] L[i+1] = b ∨
  p L[i-1] L[i] = b ∧ p L[i] L[i+1] = a := by
  induction' L with head tail ih generalizing i a b
  · simp at hi
  simp_rw [List.getElem_cons]
  simp_all +arith
  specialize @ih b a (alternates_tail h)
  repeat any_goals split
  · linarith
  · rename_i h1 h2
    have htail : tail.length > 0 := by
      by_contra h
      simp at h
      subst h
      simp at hi
    have : i = 1 := by omega
    subst this
    simp
    left
    constructor
    · exact alternates_head h htail
    · unfold alternates at h
      split at h <;> simp_all
      apply alternates_head h.right
  · simp_all; omega
  · specialize ih (i - 1) (by simp_all +arith; omega)
    have : i - 1 + 1 = i := by omega
    simp_rw [this] at ih
    tauto

theorem chain'_of_alternates
  {V C : Type*} {p : V → V → C} {a b : C} {L : List V} (h : alternates p a b L) :
  List.Chain' (fun x y ↦ p x y = a ∨ p x y = b) L := by
  fun_induction alternates <;> simp_all
  rename_i ih
  simp_rw [or_comm] at ih
  assumption
