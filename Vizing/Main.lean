import Vizing.Graph
import Vizing.EdgeColoring
import Vizing.Fan
import Vizing.Path

open Graph
open EdgeColoring

variable (n c : Nat) (G : Graph n)

def edgeColor : EdgeColoring c :=
  let A := EdgeColoring.default c n G
  let Δ := maxDegree n G
  let E := edgeSet n G
  extend A Δ E where
  extend : (EdgeColoring c) → Nat → List (Edge n) → (EdgeColoring c)
  | C, _, [] => C
  | C, Δ, (x, y)::E' =>
    let F := Fan.fan c n G C x y
    -- Choose free color on x and y, we know these exist (need to prove this)
    let a := sorry
    let b := sorry
    -- dbg_trace s!"free colors chosen: {c} {d}"
    let P := cdPath c n G C x a b
    let C' := invertPath c n C P a b
    let F' := Fan.subfan c n G C' F b
    let C'' := Fan.rotateFan c n F' C' x b
    extend C'' Δ E'
