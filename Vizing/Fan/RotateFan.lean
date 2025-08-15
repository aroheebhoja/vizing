import Vizing.Fan.Defs

namespace Fan
open Graph
open EdgeColoring
open Aux

variable
  {n c : Nat} {G : Graph n} {C : EdgeColoring c G} {x y : Vertex n}
  (F : Fan C x y)

/-
Given a fan F[1:k] of a vertex X, the "rotate fan" operation does the
following: for i = 1, ..., k–1, assign the color of (X,F[i + 1]) to
edge (X,F[i]). Finally, uncolor (X, F[k]).

This operation leaves the coloring valid because, by the definition of
a fan, the color of (X,F[i+1]) was free on F[i].
-/

def removeLast (F : Fan C x y) (h : F.val.size > 1) : Fan C x y where
  val := F.val.pop
  nborsAx := by
    intro u h
    apply F.nborsAx
    exact List.mem_of_mem_dropLast h
  nonemptyAx := by
    apply Array.size_pos_iff.mp
    simpa
  firstElemAx := by
    simp
    exact F.firstElemAx
  colorAx := by
    simp [colorAx]
    apply List.Chain'.prefix
    exact F.colorAx
    exact List.dropLast_prefix F.val.toList
  nodupAx := by
    apply dropLast_nodup_of_nodup
    exact F.nodupAx

theorem last_present (F : Fan C x y) :
  present G (x, (last F)) := by
  simp_rw [present, present_symm G (x, last F), and_self, last]
  apply F.nborsAx
  simp

theorem not_in_fan (F : Fan C x y) : x ∉ F.val := by
  intro h
  have h1 := F.nborsAx h.val
  have h2 := G.noSelfLoopsAx x
  simp [nbhd] at h1
  contradiction

def mkFan (a : Color c)
  (hvalid : edgeColorValid C (x, last F) a) (hsize : F.val.size > 1):
  Fan (setEdgeColor C (x, last F) a (last_present F) hvalid) x y where
  val :=  F.val.pop
  nborsAx := by
    simp
    intro u h
    apply F.nborsAx
    exact List.mem_of_mem_dropLast h
  nonemptyAx := by
    simp
    apply Array.size_pos_iff.mp
    simpa
  firstElemAx := by
    simp
    exact F.firstElemAx
  nodupAx := by
    simp
    apply dropLast_nodup_of_nodup
    exact F.nodupAx
  colorAx := by
    have aux1 := freeColors_invariant C (x, last F) a (last_present F) hvalid
    have aux2 := color_invariant C (x, last F) a (last_present F) hvalid
    have aux3 := getLast_not_mem_dropLast_of_nodup (by simp; exact F.nonemptyAx) F.nodupAx
    have aux4 := not_in_fan F
    apply chain'_prefix (List.dropLast_prefix F.val.toList) (R := fan_prop C x)
    · intro a b ⟨h1, h2⟩ h3
      simp_all
      rwa [← aux1, ← aux2]
      any_goals simp_all [last, Array.getLast_toList]
      · contrapose! h2
        rwa [h2]
      · intro h
        exfalso
        exact aux4 (Array.mem_of_getElem (Eq.symm h))
      · apply List.mem_of_mem_dropLast at h1
        contrapose! h1
        subst h1
        simpa
      · contrapose! h1
        rwa [h1]
    · exact F.colorAx

def rotateFan (C : EdgeColoring c G) (F : Fan C x y) (a : Color c)
  (hvalid : edgeColorValid C (x, last F) a)
  : EdgeColoring c G :=
  let a' := color C (x, last F)
  let C' := setEdgeColor C (x, last F) a (last_present F) hvalid
  if h : F.val.size > 1 then
  let F' := mkFan F a hvalid h
  have hvalid' : edgeColorValid C' (x, last F') a' := by
    simp [edgeColorValid, C', a']
    right
    constructor
    · have := setEdgeColor_freeOn C (x, last F) (last_present F) a hvalid ?_
      · simp at this
        exact this.left
      · apply fan_colored_edges x y F (last F)
        all_goals simp [last]
        exact back_neq F h
    · have := freeColors_invariant C (x, last F) a (last_present F) hvalid
      rw [← this]
      have := F.colorAx
      simp [last, F', mkFan, Array.back]
      apply chain'_rel_of_idx_consec (R := fan_prop C x)
      · assumption
      · apply Nat.sub_one_add_one ?_ |> Eq.symm
        exact Nat.sub_ne_zero_iff_lt.mpr h
      · simp [last, F', mkFan, -ne_eq]
        constructor
        · have := not_in_fan F
          contrapose! this
          simp [Array.back] at this
          exact Array.mem_of_getElem this
        · have := pop_back F.val F.nonemptyAx h F.nodupAx
          simp [-ne_eq] at this
          exact Ne.symm this
  rotateFan C' F' a' hvalid'
  else C'
  termination_by F.val.size
  decreasing_by
    simp [mkFan]
    exact Array.size_pos_iff.mpr F.nonemptyAx

theorem mem_of_mem_pop {α : Type*} {x : α} {xs : Array α} (h : x ∈ xs.pop) : x ∈ xs := by
  rw [← Array.mem_toList_iff, Array.toList_pop] at h
  rw [← Array.mem_toList_iff]
  exact List.mem_of_mem_dropLast h

theorem rotateFan_invariant (C : EdgeColoring c G) (F : Fan C x y) (a : Color c)
  (hvalid : edgeColorValid C (x, last F) a) :
  ∀ u v : Vertex n, ¬ (u = x ∧ v ∈ F.val ∨ v = x ∧ u ∈ F.val) →
    color C (u, v) = color (rotateFan C F a hvalid) (u, v) := by
  intro u v huv
  simp at huv
  rcases huv with ⟨h1, h2⟩
  fun_induction rotateFan
  rename_i C F a hvalid a' C' hsize F' hvalid' ih
  rw [← ih]
  · simp [C']
    apply color_invariant
    constructor
    · simp only [ne_eq, Prod.mk.injEq, not_and, C']
      intro hu; subst hu
      contrapose! h1
      rw [last] at h1; rw [h1]
      simp
    · simp only [ne_eq, Prod.mk.injEq, not_and, C']
      intro hu; subst hu
      contrapose! h2
      rw [last]
      simpa
  · intro hu; subst hu
    contrapose! h1
    simp [F', mkFan] at h1
    exact ⟨rfl, mem_of_mem_pop h1⟩
  · intro hv; subst hv
    contrapose! h2
    simp [F', mkFan] at h2
    exact ⟨rfl, mem_of_mem_pop h2⟩
  rename_i C F a hvalid C' hsize
  simp [C']
  have : F.val = #[y] := by
    have : F.val.size > 0 := by
      apply Array.size_pos_iff.mpr
      exact F.nonemptyAx
    have : F.val.size = 1 := by omega
    apply Array.size_eq_one_iff.mp at this
    rcases this with ⟨a, ha⟩
    have := F.firstElemAx
    simp_all
  simp_all [last]
  apply color_invariant
  simp_all
  intro h; subst h
  simpa using h2


end Fan
