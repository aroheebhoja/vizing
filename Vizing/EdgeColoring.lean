import Vizing.Graph

namespace EdgeColoring
open Graph

/-
Implementation of a basic edge-coloring library,
where `EdgeColoring c` represents a c-edge-coloring of a graph on [n] vertices.
-/

variable (c : Nat) (n : Nat) (G : Graph n)
  (nonempty : 0 < c)

-- We choose 0 as the default value, to represent an uncolored edge

-- c + 2?
abbrev Color := Fin (c + 1)
abbrev EdgeColoring := Array (Array (Color c))

def default : EdgeColoring c :=
  mkArray G.size (mkArray G.size 0)

def allColors : List (Color c) :=
  let L := List.finRange (c + 1)
  have : 0 < c + 1 := by
    exact Nat.add_pos_left nonempty 1
  L.erase ⟨0, this⟩

variable
  (C : EdgeColoring c)
  (edgecoloring1 : C.size = n ∧ ∀ x ∈ C, x.size = n)

include edgecoloring1

theorem cx' (v : Vertex n) : v < C.size := by
  rw [(edgecoloring1).left]
  exact v.isLt

-- Accessing the color of an edge is always in bound
theorem cx (e : Edge n) : e.1 < C.size ∧
  e.2 < (C[e.1]'(cx' c n C edgecoloring1 e.1)).size := by
  constructor
  · exact cx' c n C edgecoloring1 e.1
  · rw [(edgecoloring1).right]
    · exact e.2.isLt
    · exact Array.mem_of_getElem rfl

def color (e : Edge n) :=
  have := cx c n C edgecoloring1 e
  C[e.1][e.2]

variable
  (proper1 : ∀ e, ∀ v ∈ nbors n G e.1, color c n C edgecoloring1 e = color c n C edgecoloring1 (e.1, v) → v = e.2)
  (proper2 : ∀ e, ∀ u ∈ nbors n G e.2, color c n C edgecoloring1 e = color c n C edgecoloring1 (u, e.2) → u = e.1)

def setEdgeColor (e : Edge n) (a : Color c) : EdgeColoring c :=
  let e' := (e.2, e.1)
  have := cx c n C edgecoloring1 e
  let C' := C.set e.1 <| C[e.1].set e.2 a
  have h1 : C'.size = n := by sorry
  have h2 : ∀ x ∈ C', x.size = n := by sorry
  have := cx c n C' ⟨h1, h2⟩ e'
  C'.set e'.1 <| C'[e'.1].set e'.2 a

def getIncidentColors (v : Vertex n) : List (Color c) :=
  (nbors n G v).map (fun a => color c n C edgecoloring1 (v, a))

def getNborWithColor? (v : Vertex n) (a : Color c) : Option (Vertex n) :=
  let choices := (nbors n G v).filter (fun x => color c n C edgecoloring1 (v, x) = a)
  match choices with
  | [] => none
  | u :: _ => some u

def getFreeColors (v : Vertex n) : List (Color c) :=
  let incident := getIncidentColors c n G C edgecoloring1 v
  (allColors c nonempty).filter (fun x => x ∉ incident)

def freeOn (a : Color c) (v : Vertex n) :=
  a ∈ getFreeColors c n G nonempty C edgecoloring1 v

def incidentOn (a : Color c) (v : Vertex n) :=
  a ∈ getIncidentColors c n G C edgecoloring1 v

end EdgeColoring
