import Vizing.InversionGuarantee
-- set_option linter.unusedVariables false

section

open Aux Graph EdgeColoring Fan Path

variable
  {n : Nat} {G : Graph n}

def extendColoring (E : EdgeSet G) (C : EdgeColoring (maxDegree G + 1) G)
  (h : ∀ e ∈ E.val, color C e = none) :
  EdgeColoring (maxDegree G + 1) G :=
match hE : E.val with
| [] => C
| (x, y) :: es =>
  have hterm : (remove E (x, y)).val.length < E.val.length := by
    unfold remove
    simp_rw [hE, List.cons_removeAll]
    simp [List.removeAll]
    grw [List.length_filter_le]
    omega
  have h' : ∀ e ∈ (remove E (x, y)).val, color C e = none := by sorry
  let F := maximalFan C (by apply E.reprGraphAx; rw [hE]; exact List.mem_cons_self)
  let a := (freeColorsOn C (last F)).head (existsFreeColor C (by omega) (last F))
  let b := (freeColorsOn C x).head (existsFreeColor C (by omega) x)
  have ha : a.isSome := by apply isSome_if_mem_freeColorsOn C (last F); simp [a]
  have hb : b.isSome := by apply isSome_if_mem_freeColorsOn C x; simp [b]
  if heq : a = b then
    have aux : edgeColorValid C (x, last F) a := by
      simp [edgeColorValid]; right
      constructor
      · simp [heq, b]
      · simp [a]
    let C' := (rotateFan C F a aux)
    have h' : ∀ e ∈ (remove E (x, y)).val, color C' e = none := by
      intro e he
      have he' : e ∈ E.val := by
        simp [remove, List.removeAll] at he
        exact he.left
      unfold C'
      rw [← h e he']
      apply Eq.symm; apply rotateFan_invariant
      by_contra hc
      simp [remove, List.removeAll] at h he
      rcases hc with ⟨hc, hc'⟩ | ⟨hc, hc'⟩
      · have := fan_colored_edges x y F e.2 hc' (by intro h; rw [← hc, ← h] at he; simp at he)
        rw [← hc, h e.1 e.2 he'] at this
        simp at this
      · have := fan_colored_edges x y F e.1 hc' (by intro h; rw [← hc, ← h] at he; simp at he)
        rw [← hc, color_symm, h e.1 e.2 he'] at this
        simp at this
    extendColoring (remove E (x, y)) (rotateFan C F a aux) h'
  else
    let P : Path C a b x := maximalPath C ha hb heq (by simp [b])
    let C' := invert (C := C) (x := x) ha hb heq (by simp [b])
    let F' := findSubfanWithColor C F C' P (by unfold P; apply invert_spec)
    have aux : edgeColorValid C' (x, last F') a := by
      sorry
    let C'' := (rotateFan C' F' a aux)
    have h' : ∀ e ∈ (remove E (x, y)).val, color C'' e = none := by sorry
    extendColoring (remove E (x, y)) C'' h'
termination_by
  E.val.length

theorem extendColoring_proper (E : EdgeSet G) (C : EdgeColoring (maxDegree G + 1) G)
  (h : ∀ e ∈ E.val, color C e = none)
  (e : Edge n) (h1 : e ∈ (toEdgeSet G).val)
  (h2 : e ∉ E.val → (color C e).isSome) :
  (color (extendColoring E C h) e).isSome := by
  fun_induction extendColoring
  · simp_all
  · rename_i ih
    apply ih
    sorry
  · rename_i ih
    apply ih
    sorry

def mkEdgeColoring (G : Graph n) : EdgeColoring (maxDegree G + 1) G :=
  extendColoring (toEdgeSet G) empty (by simp [color, empty])

theorem mkEdgeColoring_proper :
  ∀ e ∈ (toEdgeSet G).val, (color (mkEdgeColoring G) e).isSome := by
  intro e h
  unfold mkEdgeColoring
  apply extendColoring_proper <;> simp_all

end
