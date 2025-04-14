import Vizing.EdgeColoring
import Batteries.Data.List

open Graph
open EdgeColoring

variable (a n : Nat) (G : Graph n) (C : EdgeColoring a) (c d : Color a)
  (edgecoloring1 : C.size = n ∧ ∀ x ∈ C, x.size = n)

abbrev Path := List (Edge n)

variable
  (P : Path n)
  (path1 : P ⊆ edgeSet n G)
  (path2 : P.Nodup)
  (path3 : ∀ v, (P.filter (fun e => v = e.1 ∨ v = e.2)).length < 3)

def cdPath (x : Vertex n) (c d : Color a) :=
  let p1 := extendPath x c []
  let p2 := extendPath x d []
  p1 ++ (p2.reverse)
where extendPath (u : Vertex n) (j : Color a) (p : Path n) : Path n :=
  let us := (nbors n G u).filter (fun v => color a n C edgecoloring1 (u, v) == j)
  let k := if j == c then d else c
  match h : us with
  | [] => p
  | u'::_ =>
    let p' := (u', u) :: p
    have : ((List.erase (edgeSet n G) (u', u)).diff p).length < ((edgeSet n G).diff p).length := by
      have h1 : (u', u) ∉ p := by sorry
      have h2 : (u', u) ∈ edgeSet n G := by sorry
      have h3 : (u', u) ∈ (edgeSet n G).diff p := by
        exact List.mem_diff_of_mem h2 h1
      have h4 : (List.diff (edgeSet n G) p).length > 0 := by
        exact List.length_pos_of_mem h3
      rw [← List.diff_cons, List.diff_cons_right, List.length_erase_of_mem]
      · exact Nat.sub_one_lt_of_lt h4
      · exact h3
    extendPath u' k p'
termination_by ((edgeSet n G).diff p).length

def invertPath (C : EdgeColoring a) (h : C.size = n ∧ ∀ x ∈ C, x.size = n) (P : Path n) (c d : Color a) :=
  match P with
  | [] => C
  | (u, v)::P' =>
    let k := if color a n C h (u, v) == c then d else c
    let C' := setEdgeColor a n C h (u, v) k
    have h' : C'.size = n ∧ ∀ x ∈ C', x.size = n := by sorry
    invertPath C' h' P' c d
