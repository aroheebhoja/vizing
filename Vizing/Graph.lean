/-
Implementation of a basic library for undirected graphs on [n].
-/
import Std

namespace Graph

variable (n : Nat)
abbrev Vertex := Fin n
abbrev Edge := (Vertex n) × (Vertex n)
abbrev Nbors := List (Vertex n)
abbrev Graph := Array (Nbors n)
abbrev EdgeSet := List (Edge n)

-- Axioms: a vertex can have at most n-1 neighbors, and each neighbor is unique

-- change these to variables
variable (n : Nat) (A : Nbors n)
  (nbors1 : A.length < n-1)
  (nbors2 : A.Nodup)

-- Axiom: If we have n vertices, we have n adjacency lists in our graph representation
axiom graph1 (G : Graph n) : G.size = n

-- Accessing the adjacency list of a vertex is always in bounds
-- include n h in
theorem vx : ∀ G : Graph n, ∀ v : Vertex n, v < G.size := by
  intro G v
  rw [graph1]
  exact v.isLt

  -- ∀ u v, (u, v) ∈ E → v ∈ G[u]'(vx n G u) ∧
  --                     u ∈ G[v]'(vx n G v)

def edgeSet (G : Graph n) : EdgeSet n :=
  (G.mapFinIdx (fun u nbors h =>
  (nbors.map (fun v => (⟨u, by rw [graph1] at h; exact h⟩, v))))).toList.flatten

def nbors (G : Graph n) (v : Vertex n) := G[v]'(vx n G v)

def maxDegree (G : Graph n) :=
  let degrees := (G.map (fun nbors => nbors.length))
  match degrees.getMax? (· < ·) with
  | some d => d
  | none => 0

end Graph
