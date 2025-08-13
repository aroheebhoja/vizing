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

structure Nbors where
  val : List (Vertex n)
  sizeAx : val.length < n
  nodupAx : val.Nodup

structure Graph where
  val : Array (Nbors n)
  sizeAx : val.size = n
  symmAx : ∀ u v : Vertex n, u ∈ (val[v]).val ↔ v ∈ (val[u]).val
  noSelfLoopsAx : ∀ u : Vertex n, u ∉ (val[u]).val
end

variable {n : Nat} (G : Graph n)

def nbhd (x : Vertex n) : Nbors n :=
  G.val[x]'(by rw [G.sizeAx]; exact x.isLt)

def degree (x : Vertex n) : Fin n :=
  ⟨(nbhd G x).val.length, (by simp_rw [(nbhd G x).sizeAx])⟩

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
    have := (nbhd G x).sizeAx
    simp_all
  · rename_i _ d h
    apply List.argmax_eq_some_iff.mp at h
    rcases h with ⟨_, h, _⟩
    simp at h
    exact h x

structure EdgeSet where
  val : List (Edge n)
  reprGraphAx : ∀ e ∈ val, e.1 ∈ (nbhd G e.2).val ∧ e.2 ∈ (nbhd G e.1).val
  symmAx : ∀ e, e ∈ val ↔ e.swap ∈ val
  nodupAx : val.Nodup
  noSelfLoopsAx : ∀ e ∈ val, e.1 ≠ e.2

section
variable {G : Graph n} (E : EdgeSet G)

def remove (e : Edge n) : EdgeSet G where
  val := E.val.removeAll [e, (e.2, e.1)]
  reprGraphAx := by
    simp [List.removeAll]
    intro a b h _ _
    exact E.reprGraphAx (a, b) h
  symmAx := by
    simp [List.removeAll, List.mem_pair, Prod.eq_iff_fst_eq_snd_eq]
    intro a b
    constructor
    · intro ⟨h1, h2⟩
      constructor
      exact (E.symmAx (a, b)).mp h1
      tauto
    · intro ⟨h1, h2⟩
      constructor
      exact (E.symmAx (a, b)).mpr h1
      tauto
  nodupAx := by
    have := List.Pairwise.filter
      (l := E.val)
      (R := (fun x1 x2 ↦ x1 ≠ x2))
      (fun x ↦ !List.elem x [e, (e.2, e.1)])
    apply this
    exact E.nodupAx
  noSelfLoopsAx := by
    intro f hf
    apply E.noSelfLoopsAx
    exact List.mem_of_mem_filter hf
end

def mkEdgeSet (G : Graph n) :=
  (List.finRange n).flatMap (fun u ↦ (nbhd G u).val.map (u, ·))

theorem mkEdgeSet_spec (G : Graph n) :
  ∀ e ∈ mkEdgeSet G, e.1 ∈ (nbhd G e.2).val ∧ e.2 ∈ (nbhd G e.1).val := by
  intro e he
  simp [mkEdgeSet] at he
  rcases he with ⟨_, _, ⟨h1, h2⟩⟩
  rcases Prod.eq_iff_fst_eq_snd_eq.mp h2 with ⟨_, _⟩
  simp_all [nbhd]
  exact (G.symmAx e.2 e.1).mp h1

def toEdgeSet (G : Graph n) : EdgeSet G where
  val := mkEdgeSet G
  reprGraphAx := mkEdgeSet_spec G
  symmAx := by
    intro e
    constructor
    all_goals intro h; simp [mkEdgeSet]
    · use e.2, e.1
      constructor
      · exact (mkEdgeSet_spec G e h).left
      · simp only [Prod.swap]
    · use e.1, e.2
      constructor
      · exact (mkEdgeSet_spec G (Prod.swap e) h).left
      · simp
  nodupAx := by
    simp [mkEdgeSet, List.nodup_flatMap,
    List.pairwise_iff_forall_sublist]
    constructor
    · intro x
      apply List.Nodup.map
      · simp [Function.Injective]
      · exact (nbhd G x).nodupAx
    · intro a b h
      unfold Function.onFun List.Disjoint
      apply List.Nodup.sublist at h
      specialize h (List.nodup_finRange n)
      simp_all
      intro _ _ _ _ hc _
      exact h (Eq.symm hc)
  noSelfLoopsAx := by
    intro e he
    have aux1 := mkEdgeSet_spec G (e.1, e.2) he
    have aux2 := G.noSelfLoopsAx e.1
    simp_all [nbhd]
    contrapose! aux2
    rw [← aux2] at aux1
    exact aux1.left

variable (E : EdgeSet G) (e : Edge n)

def present := e.1 ∈ (nbhd G e.2).val ∧ e.2 ∈ (nbhd G e.1).val

theorem present_symm : e.1 ∈ (nbhd G e.2).val ↔ e.2 ∈ (nbhd G e.1).val := by
  exact G.symmAx e.1 e.2

end Graph
