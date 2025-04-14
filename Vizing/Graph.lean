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

variable (n : Nat) (A : Nbors n) (G : Graph n)
  (nbors1 : A.length < n-1)
  (nbors2 : A.Nodup)
  (graphsize : G.size = n)

include graphsize in
theorem vx : ∀ v : Vertex n, v < G.size := by
  intro v
  rw [graphsize]
  exact v.isLt

  -- ∀ u v, (u, v) ∈ E → v ∈ G[u]'(vx n G u) ∧
  --                     u ∈ G[v]'(vx n G v)

include graphsize in
def edgeSet : EdgeSet n :=
  (G.mapFinIdx (fun u nbors h =>
  (nbors.map (fun v => (⟨u, by rw [graphsize] at h; exact h⟩, v))))).toList.flatten

def nbors (v : Vertex n) := G[v]'(vx n G graphsize v)

def maxDegree (G : Graph n) :=
  let degrees := (G.map (fun nbors => nbors.length))
  match degrees.getMax? (· < ·) with
  | some d => d
  | none => 0

end Graph
