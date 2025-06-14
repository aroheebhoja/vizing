/-
Implementation of a basic library for undirected graphs on [n].
-/
import Std
import Mathlib.Data.List.MinMax
set_option linter.dupNamespace false

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

include graphsize in
def edgeSet : EdgeSet n :=
  (G.mapFinIdx (fun u nbors h =>
  (nbors.map (fun v => (⟨u, by rw [graphsize] at h; exact h⟩, v))))).toList.flatten

def nbors (v : Vertex n) := G[v]'(vx n G graphsize v)

theorem nbors_to_edgeSet : ∀ v, (nbors n G graphsize v).map (fun x => (v, x)) ⊆ edgeSet n G graphsize := by
  simp [edgeSet, nbors, List.map, List.flatten]
  intro v e h
  simp
  use (nbors n G graphsize v).map (fun x => (v, x))
  simp_all
  constructor
  use v
  have := vx n G graphsize v
  rw [graphsize] at this
  use this
  rw [nbors]
  simp
  rcases h with ⟨a, ha⟩
  use a
  rw [nbors]
  exact ha

variable
  (edgeSet_symm : ∀ u v : Vertex n, (u, v) ∈ (edgeSet n G graphsize) ↔ v ∈ nbors n G graphsize u ∧ u ∈ nbors n G graphsize v)
  (nbors_symm : ∀ u v : Vertex n, v ∈ nbors n G graphsize u ↔ u ∈ nbors n G graphsize v)

def degree (v : Vertex n) := (nbors n G graphsize v).length

def vertexSet : List (Vertex n) := List.finRange n

def maxDegree :=
  let degrees := List.map (degree n G graphsize) (vertexSet n)
  match degrees.argmax id with
  | some d => d
  | none => 0

theorem maxDegree_spec : ∀ v, degree n G graphsize v ≤ maxDegree n G graphsize := by
  intro v
  simp [maxDegree]
  have hv : v ∈ vertexSet n := by
    simp only [vertexSet, List.finRange, List.mem_ofFn, exists_eq]
  split
  case _ _ d h =>
    have := @List.argmax_eq_some_iff _ Nat _ id (List.map (degree n G graphsize) (vertexSet n)) d _
    rw [this] at h
    rcases h with ⟨_, h, _⟩
    simp at h
    exact h v hv
  case _ =>
    simp_all only [List.argmax_eq_none, List.map_eq_nil_iff, degree, Nat.le_zero_eq,
      List.length_eq_zero, List.not_mem_nil]

end Graph
