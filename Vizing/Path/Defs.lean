import Vizing.EdgeColoring

set_option linter.dupNamespace false
set_option push_neg.use_distrib true
set_option maxHeartbeats 10000000

namespace Path
open Graph
open EdgeColoring
open Aux

variable {c n : Nat} {G : Graph n} (C : EdgeColoring c G)

/-
Let c and d be colors. A cdX-path is an edge path that goes through vertex X,
only contains edges colored c or d, and is maximal.
(We cannot add any other edge with color c or d to the path.)
If neither c nor d is incident on X, there is no such path.
If such a path exists, it is unique as at most one edge of each color can be
incident on X.
-/


/-

Path : List of vertices in order, all edges between 2 adjacent vertices only
colored c or d, no duplicates

-/

variable {n c : Nat} {G : Graph n} (C : EdgeColoring c G)

section

variable
  (l : List (Vertex n)) (hl : l.Nodup)
  (a b : Color c) (hab : a.isSome ∧ b.isSome)

def colorPred :=
  l.Chain' (fun v₁ v₂ ↦ color C (v₁, v₂) = a ∨ color C (v₁, v₂) = b)

def alternatesColor : Prop :=
  aux a b l ∨ aux b a l where
@[simp]
aux (a b : Color c) : List (Vertex n) → Prop
  | v₁ :: (v₂ :: vs) => color C (v₁, v₂) = a ∧ aux b a (v₂ :: vs)
  | _ => true

include hl hab in
theorem alternatesColor_of_colorPred :
  colorPred C l a b → alternatesColor C l a b := by
  simp only [alternatesColor, colorPred]
  intro h
  induction' l with head tail ih
  · simp
  · unfold alternatesColor.aux
    split <;> simp_all
    rename_i v₁ v₂ vs hv
    rcases hv with ⟨hv1, hv2⟩
    subst hv2
    rcases h with ⟨h1, h2⟩
    cases vs
    · simpa
    · rename_i vs v₃ rest
      have := color_unique C v₂ v₁ v₃
      have aux1 : color C (v₁, v₂) ≠ none := by
        apply Option.isSome_iff_ne_none.mp
        rcases h1 with h1 | h1
        all_goals subst h1; tauto
      have aux2 : v₁ ≠ v₃ := by
        by_contra h; subst h
        rcases hl with ⟨⟨_, hc⟩, _, _⟩
        exact hc (List.mem_cons_self)
      simp_rw [Option.isSome_iff_ne_none] at hab
      rcases ih with ih | ih
      all_goals rw [color_symm, ih.left] at this; simp_all

include hl hab in
theorem colorPred_of_alternatesColor :
  alternatesColor C l a b → colorPred C l a b := by
  simp only [alternatesColor, colorPred]
  intro h
  induction' l with head tail ih
  · simp
  · apply List.chain'_cons'.mpr
    constructor
    · intro v hv
      rcases List.head?_eq_some_iff.mp (Option.mem_def.mp hv) with ⟨ys, hys⟩
      subst hys
      unfold alternatesColor.aux at h
      tauto
    · apply ih
      · simp only [List.nodup_cons] at hl
        exact hl.right
      · unfold alternatesColor.aux at h
        split at h <;> simp_all
        · rename_i v₁ v₂ vs hv
          rcases hv with ⟨hv1, hv2⟩
          subst hv2
          tauto

include hl hab in
theorem colorPred_eq_alternatesColor :
  colorPred C l a b ↔ alternatesColor C l a b := by
  constructor
  apply alternatesColor_of_colorPred; repeat assumption
  apply colorPred_of_alternatesColor; repeat assumption

end

structure Path (x : Vertex n) (a b : Color c) (h : a.isSome ∧ b.isSome) where
  val : List (Vertex n)
  containsAx : x ∈ val
  nodupAx : val.Nodup
  colorAx : alternatesColor C val a b

def singletonPath (a b : Color c) (x : Vertex n) (h : a.isSome ∧ b.isSome) :
  Path C x a b h where
  val := [x]
  containsAx := by exact List.mem_singleton.mpr rfl
  nodupAx := by exact List.nodup_singleton x
  colorAx := by simp [alternatesColor]

end Path
