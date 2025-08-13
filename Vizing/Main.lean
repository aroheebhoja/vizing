import Vizing.InversionGuarantee
-- set_option linter.unusedVariables false

section

open Aux Graph EdgeColoring Fan Path

variable
  {n : Nat} (G : Graph n)

def edgeColor (G : Graph n) : EdgeColoring (maxDegree G + 1) G :=
  extend (toEdgeSet G) empty
where extend (E : EdgeSet G) (C : EdgeColoring (maxDegree G + 1) G) :
  EdgeColoring (maxDegree G + 1) G :=
match hE : E.val with
| [] => C
| (x, y) :: _ =>
  have hterm : (remove E (x, y)).val.length < E.val.length := by
    unfold remove
    simp_rw [hE, List.cons_removeAll]
    simp [List.removeAll]
    grw [List.length_filter_le]
    omega
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
    extend (remove E (x, y)) (rotateFan C F a aux)
  else
    let P : Path C a b x := maximalPath C ha hb heq (by simp [b])
    let C' := invert (C := C) (x := x) ha hb heq (by simp [b])
    let F' := findSubfanWithColor C F C' P (by unfold P; apply invert_spec)
    have aux : edgeColorValid C' (x, last F') a := by
      sorry
    extend (remove E (x, y)) (rotateFan C' F' a aux)
termination_by
  E.val.length

end
