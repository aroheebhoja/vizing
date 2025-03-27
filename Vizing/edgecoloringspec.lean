-- import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Subgraph

variable {V : Type u} (G : SimpleGraph V) (H : SimpleGraph V) {n : ℕ}

#check G.Coloring
#check SimpleGraph.Path
#check G.edgeSet
#check G.lineGraph
#check G.incidenceSet
#check G.IsSubgraph
#check G.lineGraph_adj_iff_exists

namespace SimpleGraph

abbrev EdgeColoring (α : Type v) := (G.lineGraph).Coloring α

-- partial coloring of G : coloring of the induced subgraph on some X ⊆ V
-- we want to consider all the edges incident to the vertices we're coloring
-- so this seems reasonable I think...

abbrev PartialColoring (α : Type v) (s : Set V) := (G.induce s).Coloring α
abbrev PartialEdgeColoring (α : Type v) (s : Set (↑G.edgeSet)) := G.lineGraph.PartialColoring α s

variable {G H s}
variable {α : Type*} (C : G.EdgeColoring α) (C' : G.PartialEdgeColoring α s)

theorem EdgeColoring.valid {e f : ↑G.edgeSet} (h : G.lineGraph.Adj e f) : C e ≠ C f :=
  C.map_rel h

def EdgeColorable (n : ℕ) : Prop := Nonempty (G.EdgeColoring (Fin n))

noncomputable def edgeChromaticNumber : ℕ∞ := ⨅ n ∈ setOf G.EdgeColorable, (n : ℕ∞)

-- This seems somewhat reasonable???????
def Colored (e : ↑G.edgeSet) : Prop := e ∈ s

-- Need some theorems about partial colorings???? idk

/-
*Probably only useful for the algorithm*

IncidentColors : v → EdgeColoring → Set (Set color)
· colors of G.incidenceSet v

FreeColors : v → EdgeColoring → Set (Set color)
· Set color - IncidentColors v

Fan (x : V) (K : EdgeColoring)
· Nonempty sequence of vertices f0, ..., fk (should this be an array?)
· {x, f0} is uncolored
· {x, fi+1} is colored with some c ∈ FreeColors fi

Maximal : Fan → Prop

AlternatingPath x c d : V → α → α → Path
· maximal path going through x that only contains edges colored with c and d

-/

-- If my graph and my coloring are supposed to be finite should I generalize
-- this definition or should I just define everything separately for this specific case

#check G.incidenceSet

#check Set.image

#check incidenceSet_subset

#check Coe

def incidentColors (v : V) : Set α :=
  {c : α | ∃ e, ∃ h' : e ∈ G.incidenceSet v,
           ∃ h : ⟨e, incidenceSet_subset _ _ h'⟩ ∈ s,
           c = C' ⟨⟨e, incidenceSet_subset _ _ h'⟩, h⟩}

def freeColors (v : V) : Set α := {c : α | c ∉ incidentColors C' v}

def fan (v : V) := true

#check Walk.edges

-- How to get even and odd indexed elements of a list?
def isAlternatingPath (P : Walk G a b) (v : V) (c : α) (d : α) :=
  P.IsPath ∧ v ∈ P.support
  -- even indexed elements colored with c, odd indexed elements colored with d
  -- or vice versa

-- is maximal alternating path: P a and b is an alternating path and cannot be
-- extended by any of the other edges incident to a or b

  -- Set.image C' (G.incidenceSet v ∩ s)

/-
Subroutines to implement:

These seem like they would require choice but I probably want these to be
computable
- use encodable choose

Construct a maximal fan on a vertex x
· choose an uncolored edge {x, f0} in G.incidenceSet x
· choose a color c in the free colors of f0,
  if there exists an edge {x, f1} colored c in G.incidenceSet x
  and f1 is not in the fan, add f1 to the fan
· stop when we can no longer find an incident edge {x, u} colored with any of the
  free colors of our current vertex, where u is not in the fan already

Rotating the fan
· suppose F = {f0, ..., fk} is a fan on x with k vertices
· for i ∈ {0, ..., k-1}, assign the color of {x, fi+1} to {x, fi}
· uncolor {x, fk}

Inverting the AlternatingPath
· suppose P is an AlternatingPath with colors c d
· if {pi, pi+1} was colored c, switch it to d, and vice versa

-/
