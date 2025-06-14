/-

Let's simplify.


The algorithm:
1. Pick an uncolored edge {x, y}.
2. Create a maximal fan F on x, starting with y and ending with z.
3. Let c be a free color on x and d be a free color on z.
4. Form and invert a cd-path going through x.
5. Find the minimal subfan of F and rotate it down.
6. Color {x, y} with d.

Let's represent graphs as a

Let's represent edge colorings as a flat n-by-n array that we view as a 2d array.

-/

import Std

section

variable (n : Nat)

abbrev Vertex := Fin n
abbrev Color := Nat
abbrev Graph := Fin n → List (Vertex n)
-- abbrev EdgeSet := List (Vertex × Vertex)

variable (G : Graph n) (X : List (Vertex n × Vertex n))

def equalReprAx := ∀ e ∈ X, e.2 ∈ G e.1



abbrev Test := Fin n → Fin n → Option Color



variable (M : Test n)

def symmetryAx := ∀ u v, M u v = M v u




-- def symmetryAx (M : Test n) := ∀ u v, M u v = M v u

-- def sizeAx (M : Array (Array α)) := M.size = n ∧ ∀ x ∈ M, x.size = n
-- def symmetryAx (M : Array α) := ∀ u v : Nat, u < n ∧ v < n → M[u]?[v]? = M[v]?[u]?

-- abbrev EdgeColoring := { xs : Array (Array α) // sizeAx n xs }

end
