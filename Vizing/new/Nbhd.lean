import Vizing.new.Graph
import Mathlib.Data.List.Lemmas
import Mathlib.Data.Finset.Card
import Vizing.new.Upstream

set_option linter.dupNamespace false

namespace Nbhd
open Graph

/-
Defining some useful lemmas about colored neighborhoods,
and the notion of a valid edge coloring,
where `EdgeColoring c` represents a c-edge-coloring of a graph on [n] vertices.
-/

variable (n : Nat) (c : Nat) (G : Graph n)
abbrev Color := Option (Fin c)

instance : DecidableEq (Color c) := by
  infer_instance

structure EdgeColoring where
  val : Array (Array (Color c))
  sizeAx1 : val.size = n
  sizeAx2 : ∀ i : Fin n, val[i].size = n
  representsEdgesAx : ∀ e : Edge n,
    ((val[e.1]'(by
    rw [sizeAx1]; exact e.1.isLt))[e.2]'(by
    rw [sizeAx2]; exact e.2.isLt)).isSome → present n G e
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

variable (C : EdgeColoring n c G)

def color (e : Edge n) :=
  (C.val[e.1]'(by rw [C.sizeAx1]; exact e.1.isLt))[e.2]'
  (by rw [C.sizeAx2]; exact e.2.isLt)

def coloredNbors (v : Vertex n) : Nbors n :=
  have := G.prop.right
  let NV := (C.val[v]'(by rw [C.sizeAx1]; exact v.isLt))
  have aux2 : NV.size = n := by
    exact C.sizeAx2 v
  have aux3 : ∀ x : Vertex n, x < NV.size := by
    simp_all
  let N := (List.finRange n).filter (fun x => (NV[x]'(aux3 x)).isSome)
  have ax1 : nborsSizeAx n N := by
    have h4: v ∉ N := by
      have := C.representsEdgesAx (v, v)
      have this' := G.prop.right v
      simp_all [N, present, nbhd]
      exact this
    have h5 : N.length ≤ (List.finRange n).length := by
      apply List.length_filter_le
    rcases lt_or_eq_of_le h5 with (h5 | h5)
    · simp_all; assumption
    · unfold N at h4 h5
      apply List.length_filter_eq_length_iff.mp at h5
      specialize h5 v (by exact List.mem_finRange v)
      simp_all
  have ax2 : nborsRepeatsAx n N := by
    apply List.Nodup.filter
    exact List.nodup_finRange n
  ⟨N, ⟨ax1, ax2⟩⟩

def incidentColorsOn (v : Vertex n) :=
  ((C.val[v]'(by rw [C.sizeAx1]; exact v.isLt)).filterMap id).toList

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
  incidentColorsOn n c G C v =
  (coloredNbors n c G C v).val.filterMap (fun x => color n c G C (v, x)) := by
  unfold incidentColorsOn coloredNbors color
  simp_all [List.filterMap_filter]
  simp_all [List.filterMap_filter, Option.isSome_iff_ne_none]
  have := nbhd_to_indexed_nbhd n c v C.val C.sizeAx1 C.sizeAx2
  simp_all; congr
  funext x
  split_ifs
  · assumption
  · rfl

theorem colored_nbors_subset_nbors (v : Vertex n) :
  (coloredNbors n c G C v).val ⊆ (nbhd n G v).val := by
  simp [coloredNbors]
  intro x h'
  have := C.representsEdgesAx (v, x)
  simp_all [present]

theorem colored_nbhd_size_le (v : Vertex n) :
  (coloredNbors n c G C v).val.length ≤ degree n G v := by
  let N := coloredNbors n c G C v
  let X := nbhd n G v
  simp [degree]
  apply nodup_subset_eq_length_le
  · exact N.prop.right
  · exact colored_nbors_subset_nbors n c G C v

def default : EdgeColoring n c G where
  val := Array.replicate n (Array.replicate n none)
  sizeAx1 := by simp only [Array.size_replicate]
  sizeAx2 := by simp
  representsEdgesAx := by simp
  validAx := by simp
  symmAx := by simp
