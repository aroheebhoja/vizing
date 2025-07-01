import Vizing.Path.Defs

namespace Path
open Graph
open EdgeColoring
open Aux

variable {c n : Nat} (G : Graph n) (C : EdgeColoring c G)
/-
Function: convert vertex path to edge path
[a, b, c, d] -> [(a, b), (b, c), (c, d)]
-/

/-
Invert path: partition edge path into a edges and b edges
Uncolor all edges
Prove that a and b are now free on all interior vertices
-/

variable (a b : Color c) (x : Vertex n)

-- Takes an existing path, extends it using a color d
def extendPath (d : Color c) (P : List (Vertex n)) (h : P ≠ []) :
  List (Vertex n) :=
  let u := P.getLast h
  match (nbhd G u).val.find? (fun v => color c G C (u, v) = d) with
  | none => P
  | some z => z :: P

-- Maximal path: start at x extend using a, start at x extend using b, then join

end Path
