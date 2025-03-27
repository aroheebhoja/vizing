import Vizing.EdgeColoring

namespace Fan
open Graph
open EdgeColoring

variable (c n : Nat)

abbrev Fan := List (Vertex n)
variable (G : Graph n) (C : EdgeColoring c)

def fan (x y : Vertex n) : Fan n :=
  let N := (nbors n G x).erase (y)
  (fan' [y] N).reverse
where fan' : (Fan n) → List (Vertex n) → (Fan n)
  | f :: fs, N =>
    let freeColors := getFreeColors c n G C f
    let next := N.filter (fun u => freeColors.contains (color c n C (x, u)))
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
    let freeColors := getFreeColors c n G C f
    if a ∈ freeColors then [f] else f :: (subfan fs a)

def rotateFan (F : Fan n) (C : EdgeColoring c) (x : Vertex n) (a : Color c) : EdgeColoring c :=
  rotate (F.reverse) C a where
rotate : Fan n → EdgeColoring c → Color c → EdgeColoring c
  | [], C, _ => C
  | f :: fs, C, a =>
    let a' := color c n C (x, f)
    let C' := setEdgeColor c n C (x, f) a
    rotate fs C' a'
