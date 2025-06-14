import Vizing.Graph
import Vizing.EdgeColoring
import Vizing.Fan
import Vizing.Path

open Graph
open EdgeColoring

variable (n : Nat) (G : Graph n)
  (graphsize : G.size = n)
  (nbors_symm : ∀ u v : Vertex n, v ∈ nbors n G graphsize u ↔ u ∈ nbors n G graphsize v)
  (edgeSet_symm : ∀ u v : Vertex n, (u, v) ∈ (edgeSet n G graphsize) ↔ v ∈ nbors n G graphsize u ∧ u ∈ nbors n G graphsize v)

def edgeColor : EdgeColoring ((maxDegree n G graphsize) + 1) :=
  let c := (maxDegree n G graphsize) + 1
  let A := EdgeColoring.default c n G
  let E := edgeSet n G graphsize
  have nonempty : 0 < c := by
    exact Nat.zero_lt_succ (maxDegree n G graphsize)
  have h : A.size = n ∧ ∀ x ∈ A, x.size = n := default_spec c n G graphsize
  have hdeg : maxDegree n G graphsize < c := Nat.lt_add_one (maxDegree n G graphsize)
  have h' : coloring_valid c n G graphsize A h := default_spec' c n G graphsize
  let rec extend (C : EdgeColoring c) (h : C.size = n ∧ ∀ x ∈ C, x.size = n)
                 (h2 : coloring_valid c n G graphsize C h)
                 (E : EdgeSet n) (h3 : E ⊆ edgeSet n G graphsize) : EdgeColoring c :=
  match he : E with
  | [] => C
  | (x, y) :: E' =>
    let F := Fan.fan c n nonempty G C h graphsize x y
    have aux0 : ∀ u ∈ F, (x, u) ∈ edgeSet n G graphsize := by
      apply Fan.fan_spec
      exact edgeSet_symm
      exact nbors_symm
      have : (x, y) ∈ edgeSet n G graphsize := by
        simp at h3
        exact h3.left
      apply ((edgeSet_symm x y).mp this).left
    -- a and b should be free colors on x and y, respectively
    have := existsFreeColor c n G nonempty graphsize C h h2 hdeg
    let a := (getFreeColors c n G nonempty graphsize C h x).head (this x)
    let b := (getFreeColors c n G nonempty graphsize C h y).head (this y)
    let P := cdPath c n G C h graphsize nbors_symm x a b
    let C' := invertPath c n G C h P a b
    have h' : C'.size = n ∧ ∀ x ∈ C', x.size = n := by
      exact invertPath_spec c n G C h P a b
    have aux2 : coloring_valid c n G graphsize C' h' := by
      exact invertPath_spec' c n G graphsize
            (edgeSet n G graphsize) (fun ⦃a⦄ a ↦ a) C h h2 P a b
    let F' := Fan.subfan c n nonempty G C' h' graphsize F b
    have aux1 : ∀ u ∈ F', (x, u) ∈ edgeSet n G graphsize := by
      intro u hu
      sorry
    let C'' := Fan.rotateFan c n G C' h' graphsize aux2 F' x b aux1
    have h'' : C''.size = n ∧ ∀ x ∈ C'', x.size = n := by
      exact Fan.rotateFan_spec c n G C' h' graphsize aux2 F' x b aux1
    have aux3 : coloring_valid c n G graphsize C'' h'' := by
      exact Fan.rotateFan_spec' c n G C' h' graphsize aux2 F' x b aux1
    have aux4 : E' ⊆ edgeSet n G graphsize := by
      simp at h3
      exact h3.right
    extend C'' h'' aux3 E' aux4
  extend A h h' E (by exact fun ⦃a⦄ a ↦ a)
