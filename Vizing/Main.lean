import Vizing.FindSubfan
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
  have h' : ∀ e ∈ (remove E (x, y)).val, color C e = none := by
    intro e he
    apply h
    simp_all [remove, List.removeAll]
  let F := maximalFan C (by apply E.reprGraphAx; rw [hE]; exact List.mem_cons_self)
  have auxF : isMaximal F := by apply maximalFan_isMaximal
  let a := (freeColorsOn C (last F)).head (existsFreeColor C (by omega) (last F))
  let b := (freeColorsOn C x).head (existsFreeColor C (by omega) x)
  have ha : a.isSome := by apply isSome_if_mem_freeColorsOn C (last F); simp [a]
  have hb : b.isSome := by apply isSome_if_mem_freeColorsOn C x; simp [b]
  have auxa : a ∈ freeColorsOn C (last F) := by simp [a]
  have auxb : b ∈ freeColorsOn C x := by simp [b]
  if heq : a = b then
    have aux : edgeColorValid C (x, last F) a := by simp_all [edgeColorValid]
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
    have auxP : isMaximalPath P := by apply maximalPath_isMaximal
    let C' := invert ha hb heq auxb auxP
    have auxC' : isInverted C C' P := by apply invert_spec
    let F' := findSubfan ha hb auxb auxC' auxa (by simp_all) auxF auxP
    have aux : edgeColorValid C' (x, last F') a := by
      have : a ∈ freeColorsOn C' x := by
        apply freeColor_inv_a ha hb auxb auxC' auxP (List.mem_of_getElem P.firstElemAx) auxb
      have : a ∈ freeColorsOn C' (last F') := by
        apply a_free_on_subfan
      simp_all [edgeColorValid]
    let C'' := (rotateFan C' F' a aux)
    have h' : ∀ e ∈ (remove E (x, y)).val, color C'' e = none := by
      intro e he
      have he' : e ∈ E.val := by
        simp_all [remove, List.removeAll]
      have : color C e = none := by
        rwa [← h e]
      have aux : color C' e = none := by
        rw [← this]
        apply Eq.symm
        have : color C e ≠ a ∧ color C e ≠ b := by
          rw [this]
          rw [Option.isSome_iff_ne_none] at ha hb
          tauto
        apply inversion_invariant_of_edgeColor auxC' this
      rw [← aux]
      apply Eq.symm
      apply rotateFan_invariant
      by_contra hc
      simp [remove, List.removeAll] at h he
      rcases hc with ⟨hc, hc'⟩ | ⟨hc, hc'⟩
      · have := fan_colored_edges x y F' e.2 hc' (by intro h; rw [← hc, ← h] at he; simp at he)
        rw [← hc, aux] at this
        simp at this
      · have := fan_colored_edges x y F' e.1 hc' (by intro h; rw [← hc, ← h] at he; simp at he)
        rw [← hc, color_symm, aux] at this
        simp at this
    extendColoring (remove E (x, y)) C'' h'
termination_by
  E.val.length

theorem extendColoring_proper (E : EdgeSet G) (C : EdgeColoring (maxDegree G + 1) G)
  (he1 : ∀ e ∈ E.val, color C e = none)
  (e : Edge n) (h1 : e ∈ (toEdgeSet G).val)
  (h2 : e ∉ E.val → (color C e).isSome) :
  (color (extendColoring E C he1) e).isSome := by
  fun_induction extendColoring
  · simp_all
  · rename_i ih
    apply ih
    rename_i E C h x y es hE hterm h' F auxF a b ha hb auxa auxb h aux C' he1
    intro he2
    by_cases h : e = (x, y) ∨ e = (y, x)
    rcases h with h | h
    · rw [h]
      apply rotateFan_x_y_isSome
      assumption
    · rw [h, color_symm]
      apply rotateFan_x_y_isSome
      assumption
    apply rotateFan_isSome_of_isSome
    assumption
    simp_all [remove, List.removeAll]
  ·
    rename_i ih
    apply ih
    rename_i E C he1 x y es hE hterm h' F auxF a b ha hb auxa
      auxb hne P auxP C' auxC' F' aux C'' h''
    intro he
    unfold C''
    by_cases h : e = (x, y) ∨ e = (y, x)
    rcases h with h | h
    · rw [h]
      apply rotateFan_x_y_isSome
      assumption
    · rw [h, color_symm]
      apply rotateFan_x_y_isSome
      assumption
    apply rotateFan_isSome_of_isSome
    assumption

    -- simp_all [remove, List.removeAll]
    by_cases he2 : e ∈ pathEdges P
    · have := color_of_mem_pathEdges he2
      apply auxC'.right at he2
      grind
    · apply auxC'.left at he2
      rw [← he2]
      apply h2
      simp_all [remove, List.removeAll]

def mkEdgeColoring (G : Graph n) : EdgeColoring (maxDegree G + 1) G :=
  extendColoring (toEdgeSet G) empty (by simp [color, empty])

theorem mkEdgeColoring_proper :
  ∀ e ∈ (toEdgeSet G).val, (color (mkEdgeColoring G) e).isSome := by
  intro e h
  unfold mkEdgeColoring
  apply extendColoring_proper <;> simp_all

end
