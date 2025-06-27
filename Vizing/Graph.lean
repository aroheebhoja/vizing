/-
Implementation of a basic library for undirected graphs on [n].
-/
import Std
import Mathlib.Tactic
set_option linter.dupNamespace false

namespace Graph

abbrev Vertex (n : Nat) := Fin n
abbrev Edge (n : Nat) := (Vertex n) × (Vertex n)

section
variable (n : Nat)

def nborsSizeAx (N : List (Vertex n)) := N.length < n

-- No multi-edges
def nborsRepeatsAx (N : List (Vertex n)) := N.Nodup
def Nbors (n : Nat) := {N : List (Vertex n) // nborsSizeAx n N ∧ nborsRepeatsAx n N}

def graphSizeAx (G : Array (Nbors n)) := G.size = n
def Multigraph (n : Nat) := {G : Array (Nbors n) // graphSizeAx n G}

-- Symmetry for undirected graphs: edges are bidirectional

def graphSymmAx (G : Multigraph n) :=
  have ⟨G, h⟩ := G
  have : ∀ u : Vertex n, u.val < G.size := by
    intro u
    rw [h]
    exact u.prop
  ∀ u v : Vertex n, u ∈ (G[v]'(this v)).val ↔ v ∈ (G[u]'(this u)).val

def graphNoSelfLoopsAx (G : Multigraph n) :=
  have ⟨G, h⟩ := G
  have : ∀ u : Vertex n, u.val < G.size := by
    intro u
    rw [h]
    exact u.prop
  ∀ u : Vertex n, u ∉ (G[u]'(this u)).val

abbrev Graph := {G : Multigraph n // graphSymmAx n G ∧ graphNoSelfLoopsAx n G}

end

variable {n : Nat} (G : Graph n)

def nbhd (x : Vertex n) : Nbors n :=
  G.val.val[x]'(by rw [G.val.prop]; exact x.isLt)


def degree (x : Vertex n) : Fin n :=
  let N := nbhd G x
  have : N.val.length < n := by
    have := N.prop.left
    rwa [nborsSizeAx] at this
  ⟨N.val.length, this⟩

def maxDegree : Nat :=
  let vertexSet := List.finRange n
  let degrees := vertexSet.map (degree G)
  match degrees.argmax id with
  | none => 0
  | some d => d

theorem maxDegree_lt :
  n > 0 → maxDegree G < n := by
  intro h
  simp_all only [maxDegree]
  split
  case _ _ _ => exact h
  case _ _ k _ => simp

theorem maxDegree_spec :
  ∀ x : Vertex n, degree G x ≤ maxDegree G := by
  intro x
  simp [maxDegree]
  split
  all_goals simp_all
  · simp [degree]
    have := (nbhd G x).prop.left
    simp_all [nborsSizeAx]
  · rename_i _ d h
    apply List.argmax_eq_some_iff.mp at h
    rcases h with ⟨_, h, _⟩
    simp at h
    exact h x

-- Edges in the edge set are present in the graph
def edgeSetRepresentsGraphAx (E : List (Edge n)) :=
  ∀ e, e ∈ E → e.1 ∈ (nbhd G e.2).val ∧ e.2 ∈ (nbhd G e.1).val

-- For undirected graphs: edges go both ways
def edgeSetSymmAx (E : List (Edge n)) :=
  ∀ e, e ∈ E ↔ (e.2, e.1) ∈ E

-- No multi-edges
def edgeSetNodupAx (E : List (Edge n)) := E.Nodup

def edgeSetNoSelfLoopsAx (E : List (Edge n)) :=
  ∀ e ∈ E, e.1 ≠ e.2

abbrev EdgeSet := {E : List (Edge n) //
  edgeSetRepresentsGraphAx G E ∧ edgeSetSymmAx E ∧ edgeSetNodupAx E ∧ edgeSetNoSelfLoopsAx E}

variable (E : EdgeSet G)

def remove (e : Edge n) (h : e ∈ E.val) : EdgeSet G :=
  have ⟨E, ⟨ax1, ax2, ax3, ax4⟩⟩ := E
  let E' := E.removeAll [e, (e.2, e.1)]
  have aux1 : edgeSetRepresentsGraphAx G E' := by
    simp [E', List.removeAll, edgeSetRepresentsGraphAx]
    intro a b h _ _
    exact ax1 (a, b) h
  have aux2 : edgeSetSymmAx E' := by
    simp only [E', List.removeAll, edgeSetSymmAx]
    simp [List.mem_pair, Prod.eq_iff_fst_eq_snd_eq]
    intro a b
    constructor
    · intro ⟨h4, h5⟩
      constructor
      exact (ax2 (a, b)).mp h4
      tauto
    · intro ⟨h4, h5⟩
      constructor
      exact (ax2 (a, b)).mpr h4
      tauto
  have aux3 : edgeSetNodupAx E' := by
    have := List.Pairwise.filter
        (l := E)
        (R := (fun x1 x2 ↦ x1 ≠ x2))
        (fun x ↦ !List.elem x [e, (e.2, e.1)])
    apply this
    exact ax3
  have aux4 : edgeSetNoSelfLoopsAx E' := by
    intro e he
    apply ax4
    exact List.mem_of_mem_filter he
  ⟨E', ⟨aux1, aux2, aux3, aux4⟩⟩

def toEdgeSet (G : Graph n) : EdgeSet G :=
  let A := G.val.val
  let hsize := G.val.prop
  let ⟨h1, h2⟩ := G.prop
  let this := fun u ↦ (nbhd G u).val.map (u, ·)
  let E := (List.finRange n).flatMap this
  have ax1 : edgeSetRepresentsGraphAx G E := by
    intro e he
    simp [E, this] at he
    rcases he with ⟨_, _, ⟨h3, h4⟩⟩
    rcases Prod.eq_iff_fst_eq_snd_eq.mp h4 with ⟨_, _⟩
    simp_all [nbhd]
    exact (h1 e.2 e.1).mp h3
  have ax2 : edgeSetSymmAx E := by
    intro e
    constructor
    · intro h
      simp [E, this]
      exact (ax1 e h).left
    · intro h
      simp [E, this]
      use e.1, e.2
      have := (ax1 (e.2, e.1) h).left
      simp at this
      constructor
      · assumption
      · rfl
  have ax3 : edgeSetNodupAx E := by
    have aux : ∀ u : Vertex n, (nbhd G u).val.Nodup := by
      intro u
      exact (nbhd G u).prop.right
    apply List.nodup_flatMap.mpr
    simp [this]
    constructor
    intro u
    apply List.Nodup.map
    · simp [Function.Injective]
    · exact aux u
    simp [List.pairwise_iff_forall_sublist]
    intro a b h
    have : [a, b].Nodup := by
      apply List.Nodup.sublist
      exact h
      exact List.nodup_finRange n
    unfold Function.onFun List.Disjoint
    simp_all
    intro _ _ _ _ this' _
    exact this (Eq.symm this')
  have ax4 : edgeSetNoSelfLoopsAx E := by
    intro e he
    simp [graphNoSelfLoopsAx] at h2
    simp [edgeSetRepresentsGraphAx, nbhd] at ax1
    specialize h2 e.1
    specialize ax1 e.1 e.2 he
    contrapose! h2
    simp_all
  ⟨E, ⟨ax1, ax2, ax3, ax4⟩⟩

  variable (E : EdgeSet G)

  def present (e : Edge n) := e.1 ∈ (nbhd G e.2).val ∧ e.2 ∈ (nbhd G e.1).val

  theorem present_symm (e : Edge n) : e.1 ∈ (nbhd G e.2).val ↔ e.2 ∈ (nbhd G e.1).val := by
    have := G.prop.left
    simp [graphSymmAx] at this
    split at this
    rename_i M A h heq
    simp [nbhd]
    specialize this e.1 e.2
    simp_rw [heq]
    exact this

end Graph
