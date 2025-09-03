import Mathlib.Data.List.Lemmas

variable
  {α : Type*}
  {xs : List α}

def adjacent (u v : α) (xs : List α) :=
  (∃ i, ∃ (h : i < xs.length - 1), xs[i] = u ∧ xs[i+1] = v) ∨
  (∃ i, ∃ (h : i < xs.length - 1), xs[i] = v ∧ xs[i+1] = u)

theorem adjacent_symm (u v : α) (xs : List α) :
  adjacent u v xs ↔ adjacent v u xs := by
  constructor <;> (intro h; rcases h with ⟨i, hi, hu, hv⟩)
  · right; use i, hi
  · left; assumption
  · right; use i, hi
  · left; assumption

theorem mem_of_adjacent {u v : α} {xs : List α} (h : adjacent u v xs) :
  u ∈ xs ∧ v ∈ xs := by
  rcases h with ⟨i, hi, hu, hv⟩ | ⟨i, hi, hv, hu⟩ <;>
    exact ⟨List.mem_of_getElem hu, List.mem_of_getElem hv⟩

theorem adjacent_cons {u v x : α} {xs : List α} (h : adjacent u v xs) :
  adjacent u v (x :: xs) := by
  rcases h with ⟨i, hi, hu, hv⟩ | ⟨i, hi, hv, hu⟩
  · left
    use i + 1, (by simp; omega)
    simp [hu, hv]
  · right
    use i + 1, (by simp; omega)
    simp [hu, hv]

def allAdjacentPairs : List α → List (α × α)
  | [] => []
  | [_] => []
  | x₁ :: x₂ :: xs => (x₁, x₂) :: (x₂, x₁) :: (allAdjacentPairs (x₂ :: xs))

theorem mem_allAdjacentPairs_iff_adjacent (u v : α) (xs : List α) :
  (u, v) ∈ allAdjacentPairs xs ↔ adjacent u v xs := by
  fun_induction allAdjacentPairs
  · simp_all [adjacent]
  · simp_all [adjacent]
  rename_i x₁ x₂ xs ih
  constructor
  · intro h
    simp at h
    rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩ | h
    · subst hu hv; left
      use 0, (by simp), (by simp)
      simp
    · subst hu hv; right
      use 0, (by simp), (by simp)
      simp
    · apply adjacent_cons
      apply ih.mp
      assumption
  · intro h
    simp
    rcases h with ⟨i, h, h1, h2⟩ | ⟨i, h, h1, h2⟩
    all_goals
      rw [List.getElem_cons] at h1 h2
      simp at h2
      split at h1
      simp_all
      rename_i hi
      right; right
      apply ih.mpr
    case' case3.mpr.inl => left
    case' case3.mpr.inr => right
    all_goals
      use i - 1, (by simp at h ⊢; omega)
      rw [List.getElem_cons] at h2
      simp [hi] at h2
      simp_all
