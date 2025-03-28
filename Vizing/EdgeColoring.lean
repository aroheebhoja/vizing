import Vizing.Graph

namespace EdgeColoring
open Graph

/-
Implementation of a basic edge-coloring library,
where `EdgeColoring c` represents a c-edge-coloring of a graph on [n] vertices.
-/

variable (c : Nat) (n : Nat) (G : Graph n)

-- We choose 0 as the default value, to represent an uncolored edge
axiom nonempty : 0 < c

abbrev Color := Fin (c + 1)
abbrev EdgeColoring := Array (Array (Color c))

def default : EdgeColoring c :=
  mkArray G.size (mkArray G.size 0)

def allColors : List (Color c) :=
  let L := List.finRange (c + 1)
  L.erase ⟨0, nonempty (c+1)⟩

axiom edgecoloring1 (C : EdgeColoring c) : C.size = n ∧
  ∀ x ∈ C, x.size = n

theorem cx' (C : EdgeColoring c) (v : Vertex n) : v < C.size := by
  rw [(edgecoloring1 c n C).left]
  exact v.isLt

-- Accessing the color of an edge is always in bound
theorem cx (C : EdgeColoring c) (e : Edge n) : e.1 < C.size ∧
  e.2 < (C[e.1]'(cx' c n C e.1)).size := by
  constructor
  · exact cx' c n C e.1
  · rw [(edgecoloring1 c n C).right]
    · exact e.2.isLt
    · exact Array.mem_of_getElem rfl

variable (C : EdgeColoring c)

def color (e : Edge n) :=
  have := cx c n C e
  C[e.1][e.2]

axiom proper1 (e : Edge n) : ∀ v ∈ nbors n G e.1, color c n C e = color c n C (e.1, v) → v = e.2
axiom proper2 (e : Edge n) : ∀ u ∈ nbors n G e.2, color c n C e = color c n C (u, e.2) → u = e.1

def setEdgeColor (e : Edge n) (a : Color c) : EdgeColoring c :=
  let e' := (e.2, e.1)
  have := cx c n C e
  let C := C.set e.1 <| C[e.1].set e.2 a
  have := cx c n C e'
  C.set e'.1 <| C[e'.1].set e'.2 a

def getIncidentColors (v : Vertex n) : List (Color c) :=
  (nbors n G v).map (fun a => color c n C (v, a))

def getNborWithColor (v : Vertex n) (a : Color c) : Option (Vertex n) :=
  let choices := (nbors n G v).filter (fun x => color c n C (v, x) = a)
  match choices with
  | [] => none
  | u :: _ => some u

def getFreeColors (v : Vertex n) : List (Color c) :=
  let incident := getIncidentColors c n G C v
  (allColors c).filter (fun x => x ∉ incident)

def freeOn (a : Color c) (v : Vertex n) :=
  a ∈ getFreeColors c n G C v

def incidentOn (a : Color c) (v : Vertex n) :=
  a ∈ getIncidentColors c n G C v

end EdgeColoring
