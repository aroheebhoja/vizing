import Vizing.EdgeColoring
import Batteries.Data.List
set_option linter.dupNamespace false

open Graph
open EdgeColoring

variable (a n : Nat) (G : Graph n) (C : EdgeColoring a) (c d : Color a)
  (edgecoloring1 : C.size = n ∧ ∀ x ∈ C, x.size = n)
  (graphsize : G.size = n)
  (edgeSet_symm : ∀ u v : Vertex n, (u, v) ∈ (edgeSet n G graphsize) ↔
                  v ∈ nbors n G graphsize u ∧ u ∈ nbors n G graphsize v)
  (nbors_symm : ∀ u v : Vertex n, v ∈ nbors n G graphsize u ↔ u ∈ nbors n G graphsize v)

def incident (v : Vertex n) (e : Edge n) :=
  v = e.1 ∨ v = e.2

def incident' (v : Vertex n) (e : Edge n) :=
  v = e.1 || v = e.2

variable
  (edgecoloring2 : ∀ v e f, incident n v e ∧ incident n v f →
           color a n G C edgecoloring1 e ≠ color a n G C edgecoloring1 f)

abbrev CDPath := List (Edge n)

variable
  (P : CDPath n)
  (path1 : P ⊆ edgeSet n G graphsize)
  (path2 : P.Nodup)
  (path3 : ∀ v, (P.filter (fun e => v = e.1 ∨ v = e.2)).length < 3)

include edgeSet_symm in
def cdPath (x : Vertex n) (c d : Color a) :=
  have h1 : [] ⊆ edgeSet n G graphsize := by exact List.nil_subset (edgeSet n G graphsize)
  have h2 : [].Nodup := by exact List.nodup_nil
  let p1 := extendPath x c [] h1 h2
  let p2 := extendPath x d [] h1 h2
  p1 ++ (p2.reverse)
where extendPath (u : Vertex n) (j : Color a) (p : CDPath n)
      (h1 : p ⊆ edgeSet n G graphsize) (h2 : p.Nodup)
      : CDPath n :=
  let us := (nbors n G graphsize u).filter (fun v => (color a n G C edgecoloring1 (u, v) == j) ∧ ((u, v) ∉ p) ∧ ((v, u) ∉ p))
  let k := if j == c then d else c
  match h : us with
  | [] => p
  | u':: tail =>
    let p' := (u', u) :: p
    have aux1 : u' ∈ us := by
        rw [h]
        exact List.mem_cons_self u' tail
    have h3 : (u', u) ∉ p := by
      simp [us] at aux1
      obtain ⟨_, _, _, this⟩ := aux1
      exact this
    have h4 : (u', u) ∈ edgeSet n G graphsize := by
      apply nbors_to_edgeSet n G graphsize u'
      have aux2 : ∀ x ∈ us, x ∈ nbors n G graphsize u := by
        exact List.filter_subset' (nbors n G graphsize u)
      simp only [List.mem_map, Prod.mk.injEq, true_and, exists_eq_right]
      apply (nbors_symm u u').mp
      exact aux2 u' aux1
    have : ((List.erase (edgeSet n G graphsize) (u', u)).diff p).length <
           ((edgeSet n G graphsize).diff p).length := by
      have h5 : (u', u) ∈ (edgeSet n G graphsize).diff p := by
        exact List.mem_diff_of_mem h4 h3
      have h6 : (List.diff (edgeSet n G graphsize) p).length > 0 := by
        exact List.length_pos_of_mem h5
      rw [← List.diff_cons, List.diff_cons_right, List.length_erase_of_mem]
      · exact Nat.sub_one_lt_of_lt h6
      · exact h5
    have aux1 : p' ⊆ edgeSet n G graphsize := by
      rw [List.cons_subset]
      exact ⟨h4, h1⟩
    have aux2 : p'.Nodup := by
      rw [List.nodup_cons]
      constructor
      exact h3
      exact h2
    extendPath u' k p' aux1 aux2
termination_by ((edgeSet n G graphsize).diff p).length

def invertPath (C : EdgeColoring a) (h : C.size = n ∧ ∀ x ∈ C, x.size = n) (P : CDPath n) (c d : Color a) :=
  match P with
  | [] => C
  | (u, v)::P' =>
    let k := if color a n G C h (u, v) == c then d else c
    let C' := setEdgeColor a n G C h (u, v) k
    have h' : C'.size = n ∧ ∀ x ∈ C', x.size = n := by
      exact setEdgeColor_spec a n G C h (u, v) k
    invertPath C' h' P' c d

theorem invertPath_spec (C : EdgeColoring a) (h : C.size = n ∧ ∀ x ∈ C, x.size = n) (P : CDPath n) (c d : Color a) :
  (invertPath a n G C h P c d).size = n ∧ ∀ x ∈ (invertPath a n G C h P c d), x.size = n := by
  rw [invertPath.eq_def]
  induction P generalizing C c d with
  | nil => exact h
  | cons p ps ih =>
    let (u, v) := p
    dsimp -zeta
    lift_lets
    intro k C'
    have := invertPath.proof_2 a n G C h c d u v
    obtain ⟨ih1, ih2⟩ := ih C' this c d
    rw [← invertPath.eq_def] at ih1 ih2
    constructor
    · exact ih1
    · exact ih2

def invertPath_spec' (C : EdgeColoring a)
                     (h1 : C.size = n ∧ ∀ x ∈ C, x.size = n)
                     (h2 : coloring_valid a n G graphsize C h1)
                     (P : CDPath n) (c d : Color a) :
  coloring_valid a n G graphsize (invertPath a n G C h1 P c d)
  (invertPath_spec a n G C h1 P c d):= by
  unfold invertPath
  induction P generalizing C c d with
  | nil => exact h2
  | cons p ps ih =>
    let (u, v) := p
    dsimp -zeta
    lift_lets
    intro k C'
    have aux1 := invertPath.proof_2 a n G C h1 c d u v
    have aux2 : coloring_valid a n G graphsize C' aux1 := by
      unfold C'
      apply setEdgeColor_spec' a n G graphsize C h1 h2 (u, v) k
      have : (u, v) ∈ P := by sorry
      exact path1 this
    have := ih C' aux1 aux2 c d
    unfold invertPath
    exact this
