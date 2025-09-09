import Vizing.InversionGuarantee

open Aux Graph EdgeColoring Fan Path

variable
  {n c : Nat} {G : Graph n} {C : EdgeColoring c G}
  {x y : Vertex n} {a b : Color c} (ha : a.isSome) (hb : b.isSome)
  (hfree : b ∈ freeColorsOn C x)

def mkSubfan (F : Fan C x y) (P : Path C a b x) : Array (Vertex n) :=
  match Array.findFinIdx? (fun u ↦ color C (x, u) = a) F.val with
  | some i => if F.val[i.val - 1] ∈ P.val then F.val else Array.extract F.val 0 i
  | none => F.val

include ha hb hfree in
theorem mkSubfan_colorAx {F : Fan C x y} {P : Path C a b x} {C' : EdgeColoring c G}
  (h1 : isInverted C C' P)
  (h2 : a ∈ freeColorsOn C (last F)) (h3 : isMaximal F) (h4 : color C (x, y) = none)
  (h5 : isMaximalPath P):
  colorAx C' (mkSubfan F P) x := by
  fun_cases mkSubfan
  · rename_i i heq hmem
    simp only [Array.findFinIdx?_eq_some_iff, Fin.getElem_fin, decide_eq_true_eq] at heq
    apply (inversion_guarantee_of_exists_and_mem_path ha hb F h1 h2 h3 h4 heq.left hmem h5 hfree).right
  · rename_i i heq hnmem
    simp only [Array.findFinIdx?_eq_some_iff, Fin.getElem_fin, decide_eq_true_eq] at heq
    apply (inversion_guarantee_of_exists_and_not_mem_path ha F h1 h4 heq.left hnmem hfree).right
  · rename_i heq
    simp only [Array.findFinIdx?_eq_none_iff] at heq
    apply (inversion_guarantee_of_not_exists ha F h1 h2 h3 h4 (by aesop)).right

def findSubfan {F : Fan C x y} {C' : EdgeColoring c G} {P : Path C a b x}
  (h1 : isInverted C C' P) (h2 : a ∈ freeColorsOn C (last F))
  (h3 : color C (x, y) = none)
  (hf : isMaximal F)
  (hp : isMaximalPath P) : Fan C' x y where
  val := mkSubfan F P
  nborsAx := by
    intro v hv
    apply F.nborsAx
    fun_cases mkSubfan F P <;> simp_all only [mkSubfan, ↓reduceIte]
    apply List.mem_of_mem_take (by simpa using hv)
  nonemptyAx := by
    unfold mkSubfan
    repeat any_goals split
    · exact F.nonemptyAx
    · rename_i i heq h
      have : i.val ≠ 0 := by
        by_contra h
        simp only [Array.findFinIdx?_eq_some_iff,
          Fin.getElem_fin, decide_eq_true_eq] at heq
        simp_rw [h, F.firstElemAx] at heq
        rw [heq.left] at h3
        simp_all
      simp_all
    · exact F.nonemptyAx
  firstElemAx := by
    unfold mkSubfan
    simp_rw [← F.firstElemAx]
    grind
  colorAx := mkSubfan_colorAx ha hb hfree h1 h2 hf h3 hp
  nodupAx := by
    unfold mkSubfan
    repeat any_goals split
    · exact F.nodupAx
    · rename_i i _ _
      have := List.Sublist.nodup (List.take_sublist i F.val.toList) F.nodupAx
      simpa
    · exact F.nodupAx

theorem a_free_on_subfan {F : Fan C x y} {C' : EdgeColoring c G} {P : Path C a b x}
  (h1 : isInverted C C' P) (h2 : a ∈ freeColorsOn C (last F))
  (h3 : color C (x, y) = none)
  (hf : isMaximal F)
  (hp : isMaximalPath P) : a ∈ freeColorsOn C' (last (findSubfan ha hb hfree h1 h2 h3 hf hp)) := by
  unfold findSubfan
  rw [last, Array.back_eq_getElem]
  fun_cases mkSubfan <;> unfold mkSubfan
  · rename_i i heq hmem
    simp_rw [heq, hmem]
    simp only [↓reduceIte]
    apply (inversion_guarantee_of_exists_and_mem_path ha hb F h1 h2 hf h3 ?_ hmem hp hfree).left
    simp_all
  · rename_i i heq hnmem
    simp_rw [heq, hnmem]
    have : a ∈ freeColorsOn C' F.val[↑i - 1] := by
      apply (inversion_guarantee_of_exists_and_not_mem_path ha F h1 h3 ?_ hnmem hfree).left
      simp_all
    simp_all
  · rename_i heq
    simp_rw [heq]
    apply (inversion_guarantee_of_not_exists ha F h1 h2 hf h3 (by aesop)).left
