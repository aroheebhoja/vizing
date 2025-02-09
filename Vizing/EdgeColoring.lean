-- import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.LineGraph

variable {V : Type u} (G : SimpleGraph V) {n : ℕ}

#check G.Coloring
#check SimpleGraph.Path
#check G.edgeSet
#check G.lineGraph
#check G.incidenceSet

namespace SimpleGraph

def EdgeColoring : SimpleGraph V → α := sorry

#check G.EdgeColoring
#check G.edgeSet


/-
*Useful in general*
Want to define:

using "color" as a placeholder for some abstract type that should represent
colors

EdgeColoring : SimpleGraph V → Set color (???)
· Maps G.edgeSet to colors (from a set of colors)
· Can be partial (should I use options?)
* Vertex coloring is defined as a homomorphism from G to the complete graph on α
* Do we want to define edge coloring analogously...?
* Edge coloring of G corresponds to vertex coloring of line graph of G,
  and line graph is defined in mathlib
* Does this make it better or worse though...
* Also in the definition of vertex coloring is α a set...?

Colorable : n → Prop
· true if G can be edge colored with n colors, false otherwise

EdgeChromaticNumber
· min n such that Colorable n

Colored : e → Prop
· true if e is colored in a partial coloring
-/

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
