import Mathlib.Data.List.Lemmas
import Mathlib.Data.Finset.Card
import Vizing.Graph
import Vizing.Aux

set_option linter.dupNamespace false

namespace EdgeColoring
open Graph
open Aux

/-
Defining some useful lemmas about colored neighborhoods,
and the notion of a valid edge coloring,
where `EdgeColoring c` represents a c-edge-coloring of a graph on [n] vertices.
-/
section

variable (c : Nat)
abbrev Color := Option (Fin c)
instance : DecidableEq (Color c) := by
  infer_instance

end


section
variable {n : Nat} (c : Nat) (G : Graph n)

structure EdgeColoring where
  val : Array (Array (Color c))
  sizeAx1 : val.size = n
  sizeAx2 : ∀ i : Fin n, val[i].size = n
  representsEdgesAx : ∀ e : Edge n,
    ((val[e.1]'(by
    rw [sizeAx1]; exact e.1.isLt))[e.2]'(by
    rw [sizeAx2]; exact e.2.isLt)).isSome → present G e
  validAx :
    ∀ u v : Vertex n,
    ((val[u]'(by rw [sizeAx1]; exact u.isLt))[v]'(by rw [sizeAx2]; exact v.isLt)).isSome →
    @Array.count (Color c) _
    ((val[u]'(by rw [sizeAx1]; exact u.isLt))[v]'(by rw [sizeAx2]; exact v.isLt))
    (val[u]'(by rw [sizeAx1]; exact u.isLt)) = 1
  symmAx :
    ∀ u v : Vertex n,
    ((val[u]'(by rw [sizeAx1]; exact u.isLt))[v]'(by rw [sizeAx2]; exact v.isLt)) =
    ((val[v]'(by rw [sizeAx1]; exact v.isLt))[u]'(by rw [sizeAx2]; exact u.isLt))
deriving DecidableEq
end

variable {n c : Nat} {G : Graph n} (C : EdgeColoring c G)

def color (e : Edge n) :=
  (C.val[e.1]'(by rw [C.sizeAx1]; exact e.1.isLt))[e.2]'
  (by rw [C.sizeAx2]; exact e.2.isLt)

@[simp]
def mkColoredNbors (v : Vertex n) :=
  (List.finRange n).filter (fun x => ((C.val[v]'(by
    rw [C.sizeAx1]; exact v.isLt))[x]'(by
    rw [C.sizeAx2]; exact x.isLt)).isSome)

def coloredNbors (v : Vertex n) : Nbors n where
  val := mkColoredNbors C v
  sizeAx := by
    have h1: v ∉ (mkColoredNbors C v) := by
      have := C.representsEdgesAx (v, v)
      have this' := G.noSelfLoopsAx v
      simp_all [present, nbhd, mkColoredNbors]
    have h2 : (mkColoredNbors C v).length ≤ (List.finRange n).length := by
      apply List.length_filter_le
    rcases lt_or_eq_of_le h2 with (h2 | h2)
    · simp_all
    · unfold mkColoredNbors at h1 h2
      apply List.length_filter_eq_length_iff.mp at h2
      specialize h2 v (by exact List.mem_finRange v)
      simp_all
  nodupAx := by
    apply List.Nodup.filter
    exact List.nodup_finRange n

def incidentColorsOn (v : Vertex n) : List (Color c) :=
  ((C.val[v]'(by rw [C.sizeAx1]; exact v.isLt)).filter Option.isSome).toList

theorem nbhd_to_indexed_nbhd (v : Vertex n) (A : Array (Array (Color c)))
  (h1 : A.size = n) (h2 : ∀ i : Fin n, A[i].size = n) :
  A[v].toList = List.map (fun x ↦ A[v][x]'(by simp_all)) (List.finRange n) := by
  ext1 i
  simp [Option.map]; split
  all_goals rename_i j hj
  · apply Array.getElem?_eq_some_iff.mpr
    rcases (List.getElem?_eq_some_iff.mp hj) with ⟨h3, h4⟩
    have : i < A[v].size := by
      rw [h2]
      rwa [List.length_finRange] at h3
    use this
    congr
    simp at h4
    exact Fin.mk.inj_iff.mp h4
  · apply Array.getElem?_eq_none_iff.mpr
    have := List.getElem?_eq_none_iff.mp hj
    rw [List.length_finRange] at this
    simp_all

theorem incident_colors_of_colored_nbors (v : Vertex n) :
  incidentColorsOn C v =
  List.filter Option.isSome
  ((coloredNbors C v).val.map (fun x => color C (v, x))) := by
  simp_all [incidentColorsOn, coloredNbors, color]
  have := nbhd_to_indexed_nbhd v C.val C.sizeAx1 C.sizeAx2
  simp_all [List.filter_map]
  congr

theorem colored_nbors_subset_nbors (v : Vertex n) :
  (coloredNbors C v).val ⊆ (nbhd G v).val := by
  simp [coloredNbors]
  intro x h'
  have := C.representsEdgesAx (v, x)
  simp_all [present]

theorem colored_nbhd_size_le (v : Vertex n) :
  (coloredNbors C v).val.length ≤ degree G v := by
  let N := coloredNbors C v
  let X := nbhd G v
  simp [degree]
  apply length_le_length_of_nodup_of_subset
  · exact N.nodupAx
  · exact colored_nbors_subset_nbors C v

def empty : EdgeColoring c G where
  val := Array.replicate n (Array.replicate n none)
  sizeAx1 := by simp only [Array.size_replicate]
  sizeAx2 := by simp
  representsEdgesAx := by simp
  validAx := by simp
  symmAx := by simp

end EdgeColoring
