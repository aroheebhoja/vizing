import Vizing.Graph
import Vizing.EdgeColoring.SetColor

namespace EdgeColoring
open Graph
open Aux

variable {n : Nat} {c : Nat} {G : Graph n} (C : EdgeColoring c G)

theorem incidentColors_invariant (e : Edge n) (a : Color c)
  (hpres : present G e) (hvalid : edgeColorValid C e a) :
  ∀ v : Vertex n, v ≠ e.1 ∧ v ≠ e.2 → incidentColorsOn C v =
    incidentColorsOn (setEdgeColor C e a hpres hvalid) v := by
  intro v _
  simp [incidentColorsOn, setEdgeColor]
  have := setEdge_spec4 C e a v (by tauto)
  rw [this]

theorem freeColors_invariant (e : Edge n) (a : Color c)
  (hpres : present G e) (hvalid : edgeColorValid C e a) :
  ∀ v : Vertex n, v ≠ e.1 ∧ v ≠ e.2 → freeColorsOn C v =
    freeColorsOn (setEdgeColor C e a hpres hvalid) v := by
  intro v h
  simp only [freeColorsOn]
  rw [incidentColors_invariant C e a hpres hvalid v h]

theorem color_invariant (e : Edge n) (a : Color c)
  (hpres : present G e) (hvalid : edgeColorValid C e a) :
  ∀ f : Edge n, f ≠ e ∧ f ≠ (e.2, e.1) →
  color C f = color (setEdgeColor C e a hpres hvalid) f := by
  intro f h
  simp [setEdgeColor]
  apply setEdge_spec3
  simp_rw [ne_eq, Prod.eq_iff_fst_eq_snd_eq] at h
  tauto

theorem setEdgeColor_spec (e : Edge n) (a : Color c)
  (hpres : present G e) (hvalid : edgeColorValid C e a) :
  color (setEdgeColor C e a hpres hvalid) e = a := by
  simp [setEdgeColor, color]
  apply setEdge_spec1
  assumption

theorem setEdgeColor_symm {e : Edge n} {a : Color c}
  {hpres : present G e} {hvalid : edgeColorValid C e a} :
    setEdgeColor C e a hpres hvalid = setEdgeColor C (e.2, e.1) a
    (by simpa [present, And.comm] using hpres)
    (by simpa [edgeColorValid, And.comm] using hvalid) := by
  simp [setEdgeColor]
  rwa [setEdge_symm]

theorem newColor_not_eq_oldColor (e : Edge n) (a : Color c)
  (hvalid : edgeColorValid C e a) (hcolor : (color C e).isSome) :
  a ≠ color C e := by
  intro hc
  simp [edgeColorValid, freeColorsOn, incidentColorsOn] at hvalid
  rcases hvalid with h | h
  · rw [← Option.ne_none_iff_isSome] at hcolor
    rw [← hc, ← h] at hcolor
    contradiction
  · have aux1 : a ≠ none := by
      rcases h with ⟨⟨h, _⟩, _⟩
      rw [Option.ne_none_iff_isSome, Option.isSome_iff_exists]
      simp [allColors] at h
      rcases h with ⟨b, hb⟩
      use b; exact Eq.symm hb
    have aux2 : color C e ∈ C.val[e.1]'(by rw [C.sizeAx1]; exact e.1.isLt) := by
      simp [color]
    rcases h with ⟨⟨_, h⟩, ⟨_, _⟩⟩
    simp [aux1] at h
    unfold color at hc aux2
    rw [hc] at h
    contradiction

theorem setEdgeColor_freeOn (e : Edge n) (hpres : present G e) (a : Color c)
  (hvalid : edgeColorValid C e a) (hcolor : (color C e).isSome) :
  color C e ∈ freeColorsOn (setEdgeColor C e a hpres hvalid) e.1 ∧
  color C e ∈ freeColorsOn (setEdgeColor C e a hpres hvalid) e.2 := by
  have hne := newColor_not_eq_oldColor C e a hvalid hcolor
  simp [edgeColorValid] at hvalid
  simp_all [color, freeColorsOn, incidentColorsOn]
  have := C.validAx
  have hloop := edge_not_self_loop hpres
  have aux := set_set_spec3 n C.val C.sizeAx1 C.sizeAx2 a e.1 e.2 e.2 hloop
  repeat any_goals apply And.intro
  any_goals
    simp [allColors]
    apply Option.isSome_iff_exists.mp at hcolor
    rcases hcolor with ⟨a, ha⟩
    use a; exact Eq.symm ha
  · left
    specialize this e.1 e.2 hcolor
    apply Array.not_mem_of_count_eq_zero
    simp [setEdgeColor]
    rw [setEdge_spec5 C e a hpres]
    split_ifs <;> simp_all
  · left
    specialize this e.2 e.1 (by simp_rw [← Fin.getElem_fin, C.symmAx e.1 e.2] at hcolor; assumption)
    apply Array.not_mem_of_count_eq_zero
    simp [setEdgeColor, setEdge]
    simp_rw [← Fin.getElem_fin, count_set_set, C.symmAx]
    simp_rw [Fin.getElem_fin] at *
    simp [← aux, this]
    simp_rw [← Fin.getElem_fin, C.symmAx e.1 e.2, Fin.getElem_fin] at hne
    exact hne

theorem old_color_valid {e : Edge n} {a : Color c}
  {hpres : present G e} {hvalid : edgeColorValid C e a} :
    edgeColorValid (setEdgeColor C e a hpres hvalid) e (color C e) := by
  simp [edgeColorValid]
  by_cases h : color C e = none
  · left; assumption
  · right
    exact setEdgeColor_freeOn C e hpres a hvalid (by exact Option.isSome_iff_ne_none.mpr h)


-- theorem set_unset_eq {e : Edge n} {a d : Color c}
--   {hpres : present G e} {hvalid : edgeColorValid C e a} :
--   C.val = (setEdgeColor (setEdgeColor C e a hpres hvalid) e
--     (color C e) hpres (by apply old_color_valid)).val := by
--   have aux1 : C.val.size =
--     (setEdgeColor (setEdgeColor C e a hpres hvalid) e (color C e)
--       hpres (by apply old_color_valid)).val.size := by
--     simp_all [setEdgeColor, setEdge, set_set_preserves_size]
--     exact C.sizeAx1
--   have aux2 := setEdge_sizeAx2 (setEdgeColor C e a hpres hvalid) e (color C e)
--   ext1; simp_all
--   ext1
--   · rename_i i hi hi'
--     let i' : Fin n := ⟨i, (by rwa [← C.sizeAx1])⟩
--     specialize aux2 i'
--     have := C.sizeAx2 i'
--     simp_all [setEdgeColor, setEdge, i']
--   rename_i i hi1 hi2 j hj1 hj2
--   by_cases h : (i = e.1 ∧ j = e.2) ∨ (i = e.2 ∧ j = e.1)
--   wlog hw : (i = e.1 ∧ j = e.2)
--   have : e = (e.1, e.2) := by exact?


--   specialize @this n c G C (e.2, e.1) a d (by simpa [present, And.comm] using hpres)
--     (by simpa [edgeColorValid, And.comm] using hvalid)
--   have aux3 := @setEdgeColor_symm n c G (setEdgeColor C e a hpres hvalid) e
--   have aux4 := @setEdgeColor_symm n c G C e
--   have aux5 := color_symm C e.1 e.2
--   simp at aux5
--   simp_rw [aux3, aux4, aux5]
--   apply this
--   simp_rw [← aux5]



--   -- simp at aux3
--   -- simp_rw [color_symm, ← aux3] at this
--   -- rw [setEdgeColor_symm (e := (e.2, e.1))] at this



--   -- simp_all [setEdgeColor, setEdge]





--   -- have := setEdge_spec1 C e a hpres



theorem color_incident_if {e : Edge n} {a d : Color c} {u : Vertex n}
  {hpres : present G e} {hvalid : edgeColorValid C e a}
  (h : d ∈ incidentColorsOn C u) (h2 : d ≠ color C e)
  : d ∈ incidentColorsOn (setEdgeColor C e a hpres hvalid) u := by
  by_cases h : u = e.1 ∨ u = e.2
  wlog h : u = e.1
  specialize @this _ _ _ C (e.2, e.1) a d u (by simpa [present, And.comm] using hpres)
    (by simpa [edgeColorValid, And.comm] using hvalid) (by assumption) (by rwa [color_symm])
    (by simp; tauto) (by simp_all [edge_not_self_loop hpres])
  rw [setEdgeColor_symm] at this; simpa using this
  subst h
  simp_all [incidentColorsOn, setEdgeColor]
  rcases h with ⟨h3, h4⟩
  rcases Array.getElem_of_mem h3 with ⟨i, h5, h6⟩
  simp [edgeColorValid, freeColorsOn, incidentColorsOn] at hvalid
  simp [color] at h2
  subst h6
  simp_all
  have hi' : i < n := by
    have := C.sizeAx2 ↑e.1
    simp [Fin.getElem_fin] at this; omega
  have aux1 : i ≠ ↑e.2 := by
    by_contra hc; subst hc; apply h2; rfl
  have aux2 : i ≠ e.1 := by
    by_contra hc; subst hc
    have := self_loop_uncolored C ↑e.1
    simp [color] at this
    simp [this] at h4
  have aux3 := edge_not_self_loop hpres
  apply @Array.mem_of_getElem _ _ i ?_
  rw [Eq.comm]
  apply setEdge_spec3 C e a e.1 ⟨i, (by assumption)⟩ ?_
  · simp; constructor; exact Fin.ne_of_val_ne (by tauto); left; tauto
  · have := setEdge_sizeAx2 C e a ↑e.1
    simp_all
  rw [← incidentColors_invariant C e a hpres hvalid] <;> tauto

theorem color_free_if {e : Edge n} {a d : Color c} {u : Vertex n}
  {hpres : present G e} {hvalid : edgeColorValid C e a}
  (h : d ∈ freeColorsOn C u) (h2 : a ≠ d)
  : d ∈ freeColorsOn (setEdgeColor C e a hpres hvalid) u := by
  simp_all [freeColorsOn]
  rcases h with ⟨_, h⟩
  contrapose! h
  by_cases h : u = e.1 ∨ u = e.2
  wlog h : u = e.1
  specialize @this _ _ _ C (e.2, e.1) a d u (by simpa [present, And.comm] using hpres)
    (by simpa [edgeColorValid, And.comm] using hvalid) (by assumption) (by assumption)
    (by rw [setEdgeColor_symm]; simpa) (by tauto) (by tauto)
  exact this
  subst h
  simp_all [incidentColorsOn, setEdgeColor]
  rcases h with ⟨h3, h4⟩
  rcases Array.getElem_of_mem h3 with ⟨i, h5, h6⟩
  simp [edgeColorValid, freeColorsOn, incidentColorsOn] at hvalid
  subst h6
  simp_all
  have hi' : i < n := by
    have := (setEdgeColor C e a hpres (by assumption)).sizeAx2 ↑e.1
    simp [Fin.getElem_fin, setEdgeColor] at this; omega
  have aux1 : i ≠ ↑e.2 := by
    by_contra hc; subst hc; apply h2; rw [setEdge_spec1]; assumption
  have aux2 : i ≠ e.1 := by
    by_contra hc; subst hc
    have := self_loop_uncolored (setEdgeColor C e a hpres (by assumption)) ↑e.1
    simp [color, setEdgeColor] at this
    simp [this] at h4
  have aux3 := edge_not_self_loop hpres
  apply @Array.mem_of_getElem _ _ i ?_
  apply setEdge_spec3 C e a e.1 ⟨i, (by assumption)⟩ ?_
  · simp; constructor; exact Fin.ne_of_val_ne (by tauto); left; tauto
  · have := C.sizeAx2 e.1
    simp_all
  rw [incidentColors_invariant C e a hpres hvalid] <;> tauto


end EdgeColoring
