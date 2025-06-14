import Vizing.EdgeColoring
import Mathlib.Tactic
set_option linter.dupNamespace false

namespace Fan
open Graph
open EdgeColoring

variable (c n : Nat)
 (nonempty : 0 < c)
 (G : Graph n)

section Defs

abbrev Fan := List (Vertex n)
variable (C : EdgeColoring c)
  (edgecoloring1 : C.size = n ∧ ∀ x ∈ C, x.size = n)
  (graphsize : G.size = n)
  (edgecoloring2 : coloring_valid c n G graphsize C edgecoloring1)
  (edgeSet_symm : ∀ u v : Vertex n, (u, v) ∈ (edgeSet n G graphsize) ↔ v ∈ nbors n G graphsize u ∧ u ∈ nbors n G graphsize v)
  (nbors_symm : ∀ u v : Vertex n, v ∈ nbors n G graphsize u ↔ u ∈ nbors n G graphsize v)

def fan (x y : Vertex n) : Fan n :=
  let N := (nbors n G graphsize x).erase (y)
  (fan' [y] N).reverse
where fan' : (Fan n) → List (Vertex n) → (Fan n)
  | f :: fs, N =>
    let freeColors := getFreeColors c n G nonempty graphsize C edgecoloring1 f
    let next := N.filter (fun u => freeColors.contains (color c n G C edgecoloring1 (x, u)))
    match h : next with
    | [] => (f :: fs)
    | v :: vs => have : (N.erase v).length < N.length := by
                  have h1 : v ∈ next := by
                    rw [h]
                    apply List.mem_cons_self v vs
                  have h2 : v ∈ N := by
                    simp only [List.mem_filter, next] at h1
                    exact h1.left
                  have h3 : N.length > 0 := by
                    apply List.length_pos_iff_exists_mem.mpr
                    exact ⟨v, h2⟩
                  rw [List.length_erase_of_mem]
                  · exact Nat.sub_one_lt_of_lt h3
                  · exact h2
      fan' (v :: (f :: fs)) (N.erase v)
  | _, _ => []
termination_by _ N => N.length

def subfan (F : Fan n) (a : Color c) :=
  match F with
  | [] => []
  | f :: fs =>
    let freeColors := getFreeColors c n G nonempty graphsize C edgecoloring1 f
    if a ∈ freeColors then [f] else f :: (subfan fs a)

theorem subfan_spec (F : Fan n) (a : Color c) :
  subfan c n nonempty G C edgecoloring1 graphsize F a ⊆ F := by
  unfold subfan
  simp
  induction F with
  | nil => simp
  | cons f fs ih =>
    rw [← subfan.eq_def] at ih
    simp only
    split
    simp only [List.cons_subset, List.mem_cons, true_or, List.nil_subset,
      List.subset_cons_of_subset, and_self]
    exact List.cons_subset_cons f ih

include edgeSet_symm nbors_symm in
theorem fan_spec (x y : Vertex n) (h : y ∈ nbors n G graphsize x) :
  ∀ u ∈ (fan c n nonempty G C edgecoloring1 graphsize x y),
  (x, u) ∈ edgeSet n G graphsize := by
  unfold fan fan.fan' at *
  lift_lets
  intro N freeColors next
  simp
  match h : next with
  | [] =>
    simp
    sorry
  | v :: vs =>
    dsimp
    sorry


  -- induction' h' : next with z zs ih generalizing N
  -- · intro u hu
  --   simp at hu
  --   rw [hu]
  --   apply (edgeSet_symm x y).mpr
  --   constructor
  --   exact h
  --   exact (nbors_symm x y).mp h
  -- simp_all
  -- intro u hu
  -- unfold fan.fan' at hu

  -- sorry

end Defs

def rotate (F : Fan n) (x : Vertex n) (X : EdgeColoring c)
      (h1 : X.size = n ∧ ∀ x ∈ X, x.size = n)
      (h2 : coloring_valid c n G graphsize X h1)
      (h3 : ∀ u ∈ F, (x, u) ∈ edgeSet n G graphsize)
      (a : Color c) : EdgeColoring c :=
  match h : F with
  | [] => X
  | f :: fs =>
    let a' := color c n G X h1 (x, f)
    let X' := setEdgeColor c n G X h1 (x, f) a
    have ha : X'.size = n ∧ ∀ x ∈ X', x.size = n := by
      exact setEdgeColor_spec c n G X h1 (x, f) a
    have hb : coloring_valid c n G graphsize X' ha := by
      have aux := setEdgeColor_spec' c n G graphsize X h1 h2 (x, f) a
      have : (x, f) ∈ edgeSet n G graphsize := by
        have : f ∈ f :: fs := by
          exact List.mem_cons_self f fs
        exact h3 f this
      exact aux this
    have hc : ∀ u ∈ fs, (x, u) ∈ edgeSet n G graphsize := by
      intro u hu
      have : u ∈ f :: fs := by exact List.mem_cons_of_mem f hu
      exact h3 u this
    rotate fs x X' ha hb hc a'

variable (C : EdgeColoring c)
  (edgecoloring1 : C.size = n ∧ ∀ x ∈ C, x.size = n)
  (graphsize : G.size = n)
  (edgecoloring2 : coloring_valid c n G graphsize C edgecoloring1)

def rotate_spec (F : Fan n) (x : Vertex n)
    (a : Color c) (h : ∀ u ∈ F, (x, u) ∈ edgeSet n G graphsize) :
  (rotate c n G F x C edgecoloring1 edgecoloring2 h a).size = n ∧
  ∀ y ∈ (rotate c n G F x C edgecoloring1 edgecoloring2 h a), y.size = n := by
  rw [rotate.eq_def]
  induction F generalizing C a with
  | nil => simp_all only [implies_true, and_self]
  | cons f fs ih =>
    dsimp -zeta
    lift_lets
    intro a' C'
    have aux1 := rotate.proof_1 c n G x C edgecoloring1 a f
    have aux2 := rotate.proof_3 n G x f fs h
    have aux3 := rotate.proof_2 c n G x C edgecoloring1 edgecoloring2 a f fs h aux1
    specialize @ih C' aux1 aux3 a' aux2
    rw [← rotate.eq_def] at ih
    rcases ih with ⟨ih1, ih2⟩
    constructor
    · simp [← ih1]
    · simp [← ih2]
      exact ih2

def rotateFan (F : Fan n) (x : Vertex n) (a : Color c) (h : ∀ u ∈ F, (x, u) ∈ edgeSet n G graphsize) : EdgeColoring c :=
  have : ∀ u ∈ F.reverse, (x, u) ∈ edgeSet n G graphsize := by
    intro u hu
    simp only [List.mem_reverse] at hu
    exact h u hu
  rotate c n G (F.reverse) x C edgecoloring1 edgecoloring2 this a

def rotateFan_spec (F : Fan n) (x : Vertex n) (a : Color c) (h : ∀ u ∈ F, (x, u) ∈ edgeSet n G graphsize) :
  (rotateFan c n G C edgecoloring1 graphsize edgecoloring2 F x a h).size = n ∧
  ∀ y ∈ (rotateFan c n G C edgecoloring1 graphsize edgecoloring2 F x a h), y.size = n := by
    simp [rotateFan]
    have : ∀ u ∈ F.reverse, (x, u) ∈ edgeSet n G graphsize := by
      intro u hu
      simp only [List.mem_reverse] at hu
      exact h u hu
    exact rotate_spec c n G C edgecoloring1 graphsize edgecoloring2 (List.reverse F) x a this

def rotate_spec' (F : Fan n) (x : Vertex n) (a : Color c) (h : ∀ u ∈ F, (x, u) ∈ edgeSet n G graphsize) :
  coloring_valid c n G graphsize (rotate c n G F x C edgecoloring1 edgecoloring2 h a)
  (rotate_spec c n G C edgecoloring1 graphsize edgecoloring2 F x a h):= by
  unfold rotate
  induction F generalizing C a with
  | nil => simp_all only
  | cons f fs ih =>
    dsimp -zeta
    lift_lets
    intro a' C'
    have aux1 := rotate.proof_1 c n G x C edgecoloring1 a f
    have aux2 := rotate.proof_3 n G x f fs h
    have aux3 := rotate.proof_2 c n G x C edgecoloring1 edgecoloring2 a f fs h aux1
    specialize @ih C' aux1 aux3 a' aux2
    unfold rotate
    exact ih

def rotateFan_spec' (F : Fan n) (x : Vertex n) (a : Color c) (h : ∀ u ∈ F, (x, u) ∈ edgeSet n G graphsize) :
  coloring_valid c n G graphsize (rotateFan c n G C edgecoloring1 graphsize edgecoloring2 F x a h)
  (rotateFan_spec c n G C edgecoloring1 graphsize edgecoloring2 F x a h):= by
    simp [rotateFan]
    have : ∀ u ∈ F.reverse, (x, u) ∈ edgeSet n G graphsize := by
      intro u hu
      simp only [List.mem_reverse] at hu
      exact h u hu
    exact rotate_spec' c n G C edgecoloring1 graphsize edgecoloring2 (List.reverse F) x a this

end Fan
