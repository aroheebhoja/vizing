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

def empty : EdgeColoring c G where
  val := Array.replicate n (Array.replicate n none)
  sizeAx1 := by simp only [Array.size_replicate]
  sizeAx2 := by simp
  representsEdgesAx := by simp
  validAx := by simp
  symmAx := by simp

def allColors : List (Color c) := (List.finRange c).map some

def freeColorsOn (v : Vertex n) :=
  (allColors).filter (fun x => x ∉ incidentColorsOn C v)

def findNborWithColor (v : Vertex n) (a : Color c) : Option (Vertex n) :=
  (nbhd G v).val.find? (fun v' => color C (v, v') = a)

end EdgeColoring
