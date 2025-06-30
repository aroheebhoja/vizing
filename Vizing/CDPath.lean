import Vizing.EdgeColoring

set_option linter.dupNamespace false
set_option push_neg.use_distrib true

namespace Path
open Graph
open EdgeColoring
open Aux

variable {c n : Nat} (G : Graph n) (C : EdgeColoring c G)

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
variable {n c : Nat} (G : Graph n) (C : EdgeColoring c G)

structure Path (a b : Color c) (x : Vertex n) where
  val : List (Vertex n)
  containsAx : x ∈ val
  nodupAx : val.Nodup
  -- List.Chain'
  colorAx : val.Chain' (fun x y ↦
    (color c G C (x, y) = a ∨ color c G C (x, y) = b))


-- Lemma: path is alternating

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

-- Takes an existing path and an endpoint, extends the path using a then b
def extendPath (P : Path G C a b x)
  (a b : Color c) (v : Vertex n) : Path G C a b x :=
  match (nbhd G v).val.find? (fun x => true) with
  | none => sorry
  | some x => sorry


end Path
