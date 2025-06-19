import Mathlib.Tactic

set_option linter.dupNamespace false
set_option push_neg.use_distrib true

namespace SetSet

/-
Defining a function to set a single cell in a nxn square array.
-/

variable (n : Nat) {α : Type}

def set_set (A : Array (Array α)) (h1 : A.size = n) (h2 : ∀ i : Fin n, A[i].size = n)
  (a : α) (i j : Fin n) :=
  A.set i (A[i].set j a (by rw [h2]; exact j.isLt))
  (by rw [h1]; exact i.isLt)

theorem set_set_preserves_size (A : Array (Array α))
  (h1 : A.size = n) (h2 : ∀ i : Fin n, A[i].size = n)
  (a : α) (i j : Fin n) :
  (set_set n A h1 h2 a i j).size = n ∧
  ∀ x : Fin n, ((set_set n A h1 h2 a i j)[x]'(by simp_all [set_set])).size = n := by
  have : (set_set n A h1 h2 a i j).size = n := by
    simp_all only [set_set, Fin.getElem_fin, Array.size_set]
  constructor
  · exact this
  · intro x
    simp [set_set]
    by_cases h : i = x
    · subst x
      simp only [Array.getElem_set_self, Array.size_set]
      exact h2 i
    · have := @Array.getElem_set_ne _ A i (by rw [h1]; exact i.isLt)
        (A[i].set j a (by rw [h2]; exact j.isLt)) x (by rw [h1]; exact x.isLt)
        (by exact Fin.val_ne_of_ne h)
      simp_all only [Fin.getElem_fin, Fin.is_lt]
      exact h2 x

theorem set_set_spec1 (A : Array (Array α)) (h1 : A.size = n) (h2 : ∀ i : Fin n, A[i].size = n)
  (a : α) (i j : Fin n) :
  ∀ u v : Fin n, i ≠ u ∨ j ≠ v →
  A[u][v]'(by rw [h2]; exact v.isLt) =
  ((set_set n A h1 h2 a i j)[u]'(by rw [set_set, Array.size_set, h1]; exact u.isLt))[v]'(by
    have := (set_set_preserves_size n A h1 h2 a i j).right
    rw [this]
    exact v.isLt) := by
    simp [set_set]
    intro u v h
    by_cases hi : i = u
    rcases h with (h | h)
    · contradiction
    · have := (@Array.getElem_set_ne _ A[u] j
        (by rw [h2]; exact j.isLt) a v (by rw [h2]; exact v.isLt) (by exact Fin.val_ne_of_ne h))
      simp_all
    · have := @Array.getElem_set_ne _ A i (by rw [h1]; exact i.isLt)
        (A[i].set j a (by rw [h2]; exact j.isLt)) u
        (by rw [h1]; exact u.isLt) (by exact Fin.val_ne_of_ne hi)
      simp_all

theorem set_set_spec2 (A : Array (Array α)) (h1 : A.size = n) (h2 : ∀ i : Fin n, A[i].size = n)
  (a : α) (i j : Fin n) :
  ∀ u v : Fin n, i = u ∧ j = v →
  ((set_set n A h1 h2 a i j)[u]'(by rw [set_set, Array.size_set, h1]; exact u.isLt))[v]'(by
    have := (set_set_preserves_size n A h1 h2 a i j).right
    rw [this]
    exact v.isLt) = a := by
    simp [set_set]


theorem set_set_spec3 (A : Array (Array α)) (h1 : A.size = n) (h2 : ∀ i : Fin n, A[i].size = n)
  (a : α) (i j : Fin n) : ∀ u : Fin n, i ≠ u →
  A[u] = ((set_set n A h1 h2 a i j)[u]'(by rw [set_set, Array.size_set, h1]; exact u.isLt)):= by
    simp [set_set]
    intro u h
    have := @Array.getElem_set_ne _ A i (by
      rw [h1]; exact i.isLt) (A[i].set j a (by rw [h2]; exact j.isLt))
      u (by rw [h1]; exact u.isLt) (by exact Fin.val_ne_of_ne h)
    simp_all


theorem set_set_comm (A : Array (Array α)) (h1 : A.size = n) (h2 : ∀ i : Fin n, A[i].size = n)
  (a b : α) (i j k l : Fin n) (h : k ≠ i ∨ l ≠ j) :
  set_set n (set_set n A h1 h2 a i j) (by
    exact (set_set_preserves_size n A h1 h2 a i j).left) (by
    exact (set_set_preserves_size n A h1 h2 a i j).right) b k l =
  set_set n (set_set n A h1 h2 b k l) (by
    exact (set_set_preserves_size n A h1 h2 b k l).left) (by
    exact (set_set_preserves_size n A h1 h2 b k l).right) a i j := by
  have ⟨hsize1l, hsize1r⟩ := set_set_preserves_size n A h1 h2 a i j
  have ⟨hsize2l, hsize2r⟩ := set_set_preserves_size n A h1 h2 b k l
  have ⟨l1, r1⟩ := set_set_preserves_size n (set_set n A h1 h2 b k l) (by assumption) (by assumption) a i j
  have ⟨l2, r2⟩ := set_set_preserves_size n (set_set n A h1 h2 a i j) (by assumption) (by assumption) b k l
  ext x h3 h4 y h5 h6
  simp [set_set_preserves_size]
  · apply (Nat.lt_of_lt_of_eq h4) at l1
    specialize r1 ⟨x, l1⟩
    specialize r2 ⟨x, l1⟩
    simp_all
  · let x' := Fin.mk (n := n) x (by rw [← l1]; exact h4)
    let y' := Fin.mk (n := n) y (by rw [← r1 x']; simp [x']; exact h6)
    have aux1 := set_set_spec1 n (set_set n A h1 h2 a i j) (by assumption) (by assumption) b k l x' y'
    have aux2 := set_set_spec1 n A h1 h2 a i j x' y'
    have aux3 := set_set_spec1 n (set_set n A h1 h2 b k l) (by assumption) (by assumption) a i j x' y'
    have aux4 := set_set_spec1 n A h1 h2 b k l x' y'
    have aux5 := set_set_spec2 n (set_set n A h1 h2 a i j) (by assumption) (by assumption) b k l x' y'
    have aux6 := set_set_spec2 n A h1 h2 a i j x' y'
    have aux7 := set_set_spec2 n (set_set n A h1 h2 b k l) (by assumption) (by assumption) a i j x' y'
    have aux8 := set_set_spec2 n A h1 h2 b k l x' y'
    by_cases hxy : (i ≠ x' ∨ j ≠ y') ∧ (k ≠ x' ∨ l ≠ y')
    · rcases hxy with ⟨hxy1, hxy2⟩
      specialize aux1 hxy2
      specialize aux2 hxy1
      specialize aux3 hxy1
      specialize aux4 hxy2
      simp_all [x', y']
    · push_neg at hxy
      rcases hxy with (hxy | hxy)
      · specialize aux6 hxy
        specialize aux7 hxy
        specialize aux1 (by rw [← hxy.left, ← hxy.right]; exact h)
        simp [x', y'] at aux1 aux6 aux7
        rw [← aux1, aux6, aux7]
      · specialize aux5 hxy
        specialize aux8 hxy
        specialize aux3 (by
          rw [← hxy.left, ← hxy.right]; nth_rw 1 [ne_comm];
          nth_rw 2 [ne_comm]; exact h)
        simp [x', y'] at aux5 aux8 aux3
        rw [aux5, ← aux3, aux8]

theorem count_set_set [BEq α] (A : Array (Array α))
  (h1 : A.size = n) (h2 : ∀ i : Fin n, A[i].size = n)
  (a b : α) (i j : Fin n) :
  ((set_set n A h1 h2 a i j)[i]'(by rw [set_set, Array.size_set, h1]; exact i.isLt)).count b
  = A[i].count b -
    (if (A[i][j]'(by rw [h2]; exact j.isLt) == b) = true then 1 else 0) +
    (if (a == b) = true then 1 else 0)
  := by
  simp [set_set]
  have := @Array.count_set α _ A[i] j a b (by rw [h2]; exact j.isLt)
  simp_all

theorem count_set_set' [BEq α] (A : Array (Array α))
  (h1 : A.size = n) (h2 : ∀ i : Fin n, A[i].size = n)
  (a b : α) (i j : Fin n) (h : i ≠ j) :
  ((set_set n A h1 h2 a i j)[j]'(by rw [set_set, Array.size_set, h1]; exact j.isLt)).count b
  = A[j].count b
  := by
  have := set_set_spec3 n A h1 h2 a i j j h
  rw [this]
