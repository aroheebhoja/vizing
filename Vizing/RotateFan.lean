import Vizing.Fan

namespace Fan
open Graph
open EdgeColoring
open Aux

variable
  {n c : Nat} (G : Graph n) (C : EdgeColoring c G) (x y : Vertex n)

/-

Given a fan F[1:k] of a vertex X, the "rotate fan" operation does the
following: for i = 1, ..., k–1, assign the color of (X,F[i + 1]) to
edge (X,F[i]). Finally, uncolor (X, F[k]).

This operation leaves the coloring valid because, by the definition of
a fan, the color of (X,F[i+1]) was free on F[i].


-/


end Fan
