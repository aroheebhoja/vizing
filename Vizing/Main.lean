import Vizing.Graph
import Vizing.EdgeColoring
import Vizing.Fan
import Vizing.Path

open Graph
open EdgeColoring

variable (n : Nat) (G : Graph n)

def edgeColor : EdgeColoring ((maxDegree n G) + 1) :=
  let c := (maxDegree n G) + 1
  let A := EdgeColoring.default c n G
  let E := edgeSet n G
  have nonempty : 0 < c := by
    exact Nat.zero_lt_succ (maxDegree n G)
  let rec extend : EdgeColoring c → List (Edge n) → EdgeColoring c
  | C, [] => C
  | C, (x, y)::E' =>
    have h : C.size = n ∧ ∀ x ∈ C, x.size = n := by sorry
    let F := Fan.fan c n nonempty G C h x y
    let a := sorry
    let b := sorry
    let P := cdPath c n G C h x a b
    let C' := invertPath c n C h P a b
    have h' : C'.size = n ∧ ∀ x ∈ C', x.size = n := by sorry
    let F' := Fan.subfan c n nonempty G C' h' F b
    let C'' := Fan.rotateFan c n C' F' x b
    extend C'' E'
  extend A E
