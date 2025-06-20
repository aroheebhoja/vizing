import Vizing.new.Fan

set_option linter.dupNamespace false
set_option push_neg.use_distrib true
-- set_option trace.profiler true

namespace Subfan
open Graph
open Nbhd
open EdgeColoring
open Fan

/-

A fan on (x, y) is a nonempty distinct list of vertices
that are all adjacent to x such that
the color of (x, F[i]) is free on F[i+1].

Definition/axioms for a fan, and implementation of a function that creates
a maximal fan from an edge (x, y).

-/

end Subfan
