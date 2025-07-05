import Vizing.Path.Defs

namespace Path
open Graph
open EdgeColoring
open Aux

variable {c n : Nat} {G : Graph n} (C : EdgeColoring c G)
/-
Function: convert vertex path to edge path
[a, b, c, d] -> [(a, b), (b, c), (c, d)]
-/

/-
Invert path: partition edge path into a edges and b edges
Uncolor all edges
Prove that a and b are now free on all interior vertices
-/

variable (x : Vertex n)

-- Takes an existing path, extends it using a color d
def extendPath (a b : Color c)
  (P : List (Vertex n)) (h1 : P ≠ []) (h2 : P.Nodup) :
  List (Vertex n) :=
  match hz : findNborWithColor C (P.head h1) a with
  | none => P
  -- if z is already a member of the path, we made a cycle
  | some z => if h : z ∈ P then P else
    have : (z :: P).Nodup := by
      apply List.nodup_cons.mpr ⟨_, by assumption⟩
      assumption
    extendPath b a (z :: P) (List.cons_ne_nil z P) this
termination_by (n + 1) - P.length
decreasing_by
  apply Nat.sub_succ_lt_self
  grw [List.Nodup.length_le_card h2]
  simp [Fintype.card_fin]

-- Maximal path: start at x extend using a, start at x extend using b, then join

end Path
