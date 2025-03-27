-- Implementation of a basic graph library.
/-

The idea is all the mucking around with implementation details happens here
so the implementation of the algorithm is entirely abstract.

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
axiom nbors1 (A : Nbors n) : A.length < (n-1)
axiom nbors2 (A : Nbors n) : A.Nodup

-- Axiom: If we have n vertices, we have n adjacency lists in our graph representation
axiom graph1 (G : Graph n) : G.size = n

-- Accessing the adjacency list of a vertex is always in bounds
theorem vx : ∀ G : Graph n, ∀ v : Vertex n, v < G.size := by
  intro G v
  rw [graph1]
  exact v.isLt

axiom edgeSet1 (E : EdgeSet n) (G : Graph n) :
  ∀ u v, (u, v) ∈ E → v ∈ G[u]'(vx n G u) ∧
                      u ∈ G[v]'(vx n G v)

def edgeSet (G : Graph n) : EdgeSet n :=
  (G.mapFinIdx (fun u nbors h =>
  (nbors.map (fun v => (⟨u, by rw [graph1] at h; exact h⟩, v))))).toList.flatten

def nbors (G : Graph n) (v : Vertex n) := G[v]'(vx n G v)

end Graph
