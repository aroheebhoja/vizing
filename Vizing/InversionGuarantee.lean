import Vizing.Aux
import Vizing.Graph
import Vizing.EdgeColoring
import Vizing.Fan
import Vizing.Path

open Aux Graph EdgeColoring Fan Path

variable
  {n c : Nat} {G : Graph n} {C : EdgeColoring c G}
  {x y : Vertex n} {a b : Color c} (ha : a.isSome) (hb : b.isSome)

-- Maximality : all free colors on last vertex of fan are free on x

include ha hb in
theorem freeColors_inversion_invariant {C' : EdgeColoring c G} {P : Path C a b x}
  {u : Vertex n} {d : Color c}
  (hC' : isInverted C C' P) (hu : u ≠ P.val.head (P.nonemptyAx) ∧ u ≠ P.val.getLast (P.nonemptyAx))
  (hd : d ∈ freeColorsOn C u) : d ∈ freeColorsOn C' u := by
  have : d.isSome :=
    by exact isSome_if_mem_freeColorsOn C u hd
  apply freeColor_of_not_exists_and_isSome
  · assumption
  · apply not_exists_of_freeColor at hd
    contrapose! hd
    rcases hd with ⟨v, hv⟩
    rcases hC' with ⟨hnotmem, hmem⟩
    by_cases h : (u, v) ∈ pathEdges P
    · specialize hmem (u, v) h
      rcases exists_other_nbor_of_mem_pathEdges ha hb h hu with ⟨w, hw1, hw2⟩
      use w
      apply color_of_mem_pathEdges at h
      apply color_of_mem_pathEdges at hw1
      simp_all
      grind
    · specialize hnotmem (u, v)
      use v
      rwa [hnotmem]
      assumption


theorem freeColors_inversion_invariant' {C' : EdgeColoring c G} {P : Path C a b x}
  {u : Vertex n} {d : Color c}
  (hC' : isInverted C C' P) (hd : d ≠ a ∧ d ≠ b)
  (hu : d ∈ freeColorsOn C u) : d ∈ freeColorsOn C' u := by
  have := isSome_if_mem_freeColorsOn C u hu
  apply freeColor_of_not_exists_and_isSome
  · exact this
  · apply not_exists_of_freeColor at hu
    contrapose! hu
    rcases hu with ⟨v, hv⟩
    have hpres : present G (u, v) := by
      apply C'.representsEdgesAx
      unfold color at hv
      simp at ⊢ hv
      rwa [hv]
    use v
    rw [← hv]
    apply inversion_invariant_of_edgeColor'
    any_goals assumption
    simp_all

theorem colorAx_invariant_aux
  {C' : EdgeColoring c G} {F : List (Vertex n)} (hF : F ≠ [])
  (hF2 : F.Nodup)
  (h1 : ∀ (a b : Vertex n), color C (a, b) = color C' (a, b))
  (h2 : List.Chain' (fun f₁ f₂ ↦ color C (x, f₂) ∈ freeColorsOn C f₁) F)
  (h3 : ∀ z ∈ F, z ≠ F.head hF → (color C (x, z)).isSome) :
  List.Chain' (fun f₁ f₂ ↦ color C' (x, f₂) ∈ freeColorsOn C' f₁) F := by
  rcases List.exists_cons_of_ne_nil hF with ⟨head, tail, hF⟩
  by_cases htail : tail = []
  · subst htail hF
    exact List.chain'_singleton head
  · rw [List.chain'_iff_get] at ⊢ h2
    simp at ⊢ h2
    intro i h
    specialize h2 i h
    apply freeColor_of_not_exists_and_isSome
    · rw [← h1]
      apply h3
      · simp
      · by_contra hc
        rw [List.head_eq_getElem, List.Nodup.getElem_inj_iff hF2] at hc
        linarith
    apply not_exists_of_freeColor at h2
    contrapose! h2
    rcases h2 with ⟨v, hv⟩
    use v
    simp_all

include ha hb in
theorem colorAx_invariant {C' : EdgeColoring c G} {F : Fan C x y}
  (h : ∀ (a b : Vertex n), color C (a, b) = color C' (a, b)) :
  colorAx C' F.val x := by
  apply colorAx_invariant_aux
  · exact F.nodupAx
  · assumption
  · exact F.colorAx
  · intro z hz1 hz2
    apply fan_colored_edges x y F
    · exact Array.mem_def.mpr hz1
    · contrapose! hz2
      rw [← F.firstElemAx] at hz2
      grind
  · simp only [ne_eq, Array.toList_eq_nil_iff]
    exact F.nonemptyAx

include ha in
theorem color_neq_of_fan_edge {C : EdgeColoring c G} {F : Fan C x y}
  {j : Fin F.val.size}
  (hj : color C (x, F.val[j]) = a)
  (hx : b ∈ freeColorsOn C x)
  {i : Nat} (hi1 : i < F.val.size) (hi2 : i ≠ j) :
  color C (x, F.val[i]) ≠ a ∧ color C (x, F.val[i]) ≠ b := by
  constructor
  · by_contra hc
    have : (color C (x, F.val[j])).isSome := by rwa [hj]
    rw [← hc] at hj
    apply color_unique at hj
    rcases hj with hj | hj <;> simp_all
    apply (List.Nodup.getElem_inj_iff F.nodupAx).mp at hj
    exact hi2 (Eq.symm hj)
  · apply not_exists_of_freeColor at hx
    contrapose! hx
    use F.val[i]

include ha in
theorem fan_edges_invariant {C C' : EdgeColoring c G} {F : Fan C x y} {P : Path C a b x}
  {j : Fin F.val.size}
  (hj : color C (x, F.val[j]) = a)
  (hC' : isInverted C C' P)
  (hx : b ∈ freeColorsOn C x)
  {i : Nat} (hi1 : i < F.val.size) (hi2 : i ≠ j) :
  color C (x, F.val[i]) = color C' (x, F.val[i]) := by
  apply inversion_invariant_of_edgeColor
  assumption
  exact color_neq_of_fan_edge ha hj hx hi1 hi2

include ha in
theorem maximalPath_singleton_if {C : EdgeColoring c G} {F : Fan C x y} {P : Path C a b x}
  (ha1 : a ∈ freeColorsOn C (last F))
  (hF : isMaximal F) (hxy : color C (x, y) = none)
  (hfree : ¬∃ j : Fin F.val.size, color C (x, F.val[j]) = a) :
  P.val = [x] := by
  have aux0 : a ∈ freeColorsOn C x := by
    simp [isMaximal] at hF
    by_contra hc
    simp [freeColorsOn, mem_allColors_if_isSome ha, incidentColorsOn] at hc
    rcases Array.getElem_of_mem hc.left with ⟨i, hi1, hi2⟩
    specialize hF ⟨i, (by rwa [← Fin.getElem_fin, C.sizeAx2] at hi1)⟩
    apply hF ?_ ?_ (by simpa [color, hi2])
    have := C.representsEdgesAx (x, ⟨i, (by rwa [← Fin.getElem_fin, C.sizeAx2] at hi1)⟩)
    simp [hi2, ha, present] at this
    apply (List.mem_erase_of_ne ?_).mpr
    · tauto
    · by_contra hc
      subst hc
      simp_all [color, Option.isSome_iff_ne_none]
    · contrapose! hfree
      simp [color]
      rw [← hi2]
      rcases Array.mem_iff_getElem.mp hfree with ⟨j, hj1, hj2⟩
      apply Fin.exists_iff.mpr
      use j, hj1
      simp [hj2]
  have h1 := P.nonemptyAx
  have h2 := P.colorAx
  have h3 := P.firstElemAx
  rw [alternatesColor, alternates.eq_def] at h2
  split at h2
  · contradiction
  · simp_all
  · rename_i _ v₁ v₂ vs heq
    have : v₂.val < (C.val[↑x]'(by rw [C.sizeAx1]; exact x.isLt)).size := by
      rw [C.sizeAx2]
      exact v₂.isLt
    have : a ∈ C.val[x]'(by rw [C.sizeAx1]; exact x.isLt) := by
      apply Array.mem_iff_getElem.mpr
      use v₂
      simp_all [color]
    simp_all [color, freeColorsOn, incidentColorsOn, Option.isSome_iff_ne_none]

-- @[simp]
-- theorem fan_size_eq (F : Fan C x y) : (F.val.size - 1 + 1) = F.val.size := by
--   apply Nat.sub_add_cancel
--   apply Nat.succ_le_of_lt
--   exact Array.size_pos_iff.mpr F.nonemptyAx

include ha in
theorem inversion_guarantee_of_not_exists (F : Fan C x y)
  {C' : EdgeColoring c G} {P : Path C a b x}
  (hC' : isInverted C C' P) (ha1 : a ∈ freeColorsOn C (last F))
  (hF : isMaximal F) (hxy : color C (x, y) = none)
  (hj : ¬∃ j : Fin F.val.size, color C (x, F.val[j]) = a) :
  a ∈ freeColorsOn C' (F.val[F.val.size - 1]'(by
    simp; apply Array.size_pos_iff.mpr; exact F.nonemptyAx)) ∧ colorAx C' F.val x := by
  have hP : P.val = [x] :=
    maximalPath_singleton_if ha ha1 hF hxy hj
  simp [isInverted, isInverted_notmem, isInverted_mem, hP,
    pathEdges, color, allAdjacentPairs] at hC'
  constructor
  · apply freeColor_of_not_exists_and_isSome _ ha
    apply not_exists_of_freeColor at ha1
    contrapose! ha1
    rcases ha1 with ⟨v, hv⟩
    use v
    simpa [color, last, Array.back_eq_getElem, color_symm, hC'] using hv
  · apply colorAx_invariant
    repeat assumption


theorem chain'_imp_of_mem {α : Type*} {R S : α → α → Prop}
     {l : List α} (h1 : ∀ a ∈ l, ∀ b ∈ l, R a b → S a b) (h2 : List.Chain' R l) :
    List.Chain' S l := by
    rw [List.Chain'.iff_mem] at ⊢ h2
    apply (List.Chain'.imp ?_)
    · exact h2
    · intro a b h
      tauto

include ha hb in
theorem inversion_guarantee_of_exists_and_mem_path (F : Fan C x y)
  {C' : EdgeColoring c G} {P : Path C a b x} {j : Fin F.val.size}
  (hC' : isInverted C C' P) (ha1 : a ∈ freeColorsOn C (last F))
  (hF : isMaximal F) (hxy : color C (x, y) = none)
  (hj : color C (x, F.val[j]) = a) (hp : F.val[j.val - 1] ∈ P.val)
  (hp2 : isMaximalPath P)
  (hx : b ∈ freeColorsOn C x) :
  a ∈ freeColorsOn C' (F.val[F.val.size - 1]'(by
    simp; apply Array.size_pos_iff.mpr; exact F.nonemptyAx)) ∧ colorAx C' F.val x := by
  have aux0 : j.val > 0 := by
    by_contra hc
    simp_all [F.firstElemAx, Option.isSome_iff_ne_none]
  have aux1 : a ∈ freeColorsOn C F.val[j.val - 1] := by
    rw [← hj]
    apply chain'_rel_of_idx_consec (Nat.sub_lt_of_lt j.isLt) (j.isLt) F.colorAx
    omega
  have aux2 : P.val.length > 1 := by
      by_contra hc
      have := P.firstElemAx
      have := not_in_fan F
      have : ∃ y, P.val = [y] := by
        have := List.length_pos_iff.mpr P.nonemptyAx
        exact List.length_eq_one_iff.mp (by omega)
      rcases this with ⟨y, hy⟩
      grind
  have aux3 : P.val[1]'(by omega) = F.val[j.val] := by
    have := P.colorAx
    unfold alternatesColor alternates at this
    split at this
    any_goals (rename_i heq; rw [heq] at aux2; simp at aux2)
    rename_i v₁ v₂ vs
    have hv₁ : v₁ = x := by
      have := P.firstElemAx
      aesop
    simp_all only
    have : color C (x, F.val[j.val]) = color C (x, v₂) := by
      rw [← Fin.getElem_fin, hj, this.left]
    have := color_unique C x _ _ this
    aesop
  have aux4 : F.val[j.val] ∈ P.val := by exact List.mem_of_getElem aux3
  constructor
  · apply freeColor_of_not_exists_and_isSome _ ha
    simp [isInverted, isInverted_notmem, isInverted_mem, aux1, pathEdges, color] at hC'
    rcases hC' with ⟨hC', _⟩
    have ha2 := not_exists_of_freeColor C ha1
    contrapose! ha2
    rcases ha2 with ⟨v, hv⟩
    use v
    rw [← hv]
    simp [color, last, Array.back_eq_getElem]
    apply hC'
    sorry
  · have hcolor := F.colorAx
    unfold colorAx fan_prop at ⊢ hcolor
    apply List.chain'_iff_get.mpr
    intro i hi
    simp only [Array.length_toList, List.get_eq_getElem, Array.getElem_toList]
    by_cases hij : i = j.val - 1
    · subst hij
      have : j.val - 1 + 1 = j := by omega
      simp [aux0, this]
      have aux5 : color C' (x, F.val[j.val]) = b := by
        have : (x, F.val[↑j]) ∈ pathEdges P := by
          simp [pathEdges]
          rw [mem_allAdjacentPairs_iff_adjacent]
          left
          have := P.nonemptyAx
          have := P.firstElemAx
          use 0, (by simpa)
        have := hC'.right _ this
        tauto
      rw [aux5]
      apply freeColor_inv_a ha hb hx hC' hp2 hp aux1
    · have : color C (x, F.val[i + 1]'(by grind)) = color C' (x, F.val[i + 1]'(by grind)) := by
        apply fan_edges_invariant ha hj hC' hx (by grind) (by grind)
      rw [← this]
      apply freeColors_inversion_invariant' hC' ?_
        (by apply @chain'_rel_of_idx_consec _ _ F.val.toList i (i + 1) (by omega) (by omega) hcolor; rfl)
      · apply color_neq_of_fan_edge ha hj hx (by grind) (by grind)


include ha hb in
theorem inversion_guarantee_of_exists_and_not_mem_path (F : Fan C x y)
  {C' : EdgeColoring c G} {P : Path C a b x} {j : Fin F.val.size}
  (hC' : isInverted C C' P) (hxy : color C (x, y) = none)
  (hj : color C (x, F.val[j]) = a) (hp : F.val[j.val - 1] ∉ P.val)
  (hx : b ∈ freeColorsOn C x) :
  a ∈ freeColorsOn C' (F.val[j.val - 1]'(Nat.sub_lt_of_lt j.isLt)) ∧
  colorAx C' (Array.extract F.val 0 j) x := by
  have aux0 : j.val > 0 := by
    by_contra hc
    simp_all [F.firstElemAx, Option.isSome_iff_ne_none]
  have aux1 : a ∈ freeColorsOn C F.val[j.val - 1] := by
    rw [← hj]
    apply chain'_rel_of_idx_consec (Nat.sub_lt_of_lt j.isLt) (j.isLt) F.colorAx
    omega
  constructor
  · apply freeColor_of_not_exists_and_isSome _ ha
    apply not_exists_of_freeColor at aux1
    contrapose! aux1
    rcases aux1 with ⟨v, hv⟩
    use v
    rw [← hv]
    simp [isInverted, isInverted_notmem] at hC'
    rcases hC' with ⟨hC', _⟩
    apply hC'
    contrapose! hp
    rw [pathEdges, mem_allAdjacentPairs_iff_adjacent] at hp
    apply mem_of_adjacent at hp
    tauto
  · rw [colorAx]
    unfold fan_prop
    have : List.Chain' (fun f₁ f₂ ↦ color C (x, f₂) ∈ freeColorsOn C f₁) (F.val.extract 0 ↑j).toList := by
      have := F.colorAx
      unfold colorAx fan_prop at this
      simp_all
      exact List.Chain'.take this ↑j
    apply chain'_imp_of_mem _ this
    intro z hz w hw h
    simp at hz hw
    suffices : color C (x, w) = color C' (x, w)
    rw [← this]
    apply freeColors_inversion_invariant' hC' ?_ h
    all_goals
      rcases List.getElem_of_mem hz with ⟨k, hk1, hk2⟩
      rcases List.getElem_of_mem hw with ⟨l, hl1, hl2⟩
      simp at hk1 hk2 hl1 hl2
      subst hk2 hl2
    apply color_neq_of_fan_edge ha hj hx (by omega) (by omega)
    apply fan_edges_invariant ha hj hC' hx (by omega) (by omega)

#exit

include ha hb in
theorem inversion_guarantee_of_exists (F : Fan C x y)
  {C' : EdgeColoring c G} {P : Path C a b x}
  (hC' : isInverted C C' P) (ha1 : a ∈ freeColorsOn C (last F))
  (hF : isMaximal F) (hxy : color C (x, y) = none)
  (hj : ∃ j : Fin F.val.size, color C (x, F.val[j]) = a)
  (hx : b ∈ freeColorsOn C x) :
  ∃ i : Fin F.val.size, a ∈ freeColorsOn C' F.val[i] ∧
                        colorAx C' (Array.extract F.val 0 (i+1)) x := by
  rcases hj with ⟨j, hj⟩
  have aux0 : j.val > 0 := by
    by_contra hc
    simp_all [F.firstElemAx, Option.isSome_iff_ne_none]
  have aux1 : a ∈ freeColorsOn C F.val[j.val - 1] := by
    rw [← hj]
    apply chain'_rel_of_idx_consec (Nat.sub_lt_of_lt j.isLt) (j.isLt) F.colorAx
    omega
  by_cases hp : F.val[j.val - 1] ∈ P.val
  · use ⟨F.val.size - 1, (by simp; apply Array.size_pos_iff.mpr; exact F.nonemptyAx)⟩
    constructor
    · apply freeColor_of_not_exists_and_isSome _ ha
      simp [isInverted, isInverted_notmem, isInverted_mem, aux1, pathEdges, color] at hC'
      rcases hC' with ⟨hC', _⟩
      have ha2 := not_exists_of_freeColor C ha1
      contrapose! ha2
      rcases ha2 with ⟨v, hv⟩
      use v
      rw [← hv]
      simp [color, last, Array.back_eq_getElem]
      apply hC'
      · rw [← mem_edgeSet_iff_present]
        apply C'.representsEdgesAx
        simp [color] at ⊢ hv
        rwa [hv]
      · by_contra hc
        rw [mem_allAdjacentPairs_iff_adjacent] at hc
        apply mem_of_adjacent at hc
        simp [last, Array.back] at ha1
        simp [isMaximal] at hF
        have : F.val[F.val.size - 1] ≠ F.val[j.val - 1] := by
          by_contra hc
          apply (List.Nodup.getElem_inj_iff F.nodupAx).mp at hc
          have : j = F.val.size := by omega
          have := j.isLt
          omega
        have := isLast_if C hp aux1
        have := isLast_if C hc.left ha1
        simp_all
    · simp only [fan_size_eq, Array.extract_size]
      unfold colorAx fan_prop
      apply chain'_imp_of_mem ?_
      · exact F.colorAx
      intro z hz w hw h
      rcases List.getElem_of_mem hz with ⟨k, hk1, hk2⟩
      rcases List.getElem_of_mem hw with ⟨l, hl1, hl2⟩
      simp at hk1 hk2 hl1 hl2
      subst hk2 hl2
      by_cases heq : l = j
      subst heq



      sorry

      have : color C (x, F.val[l]) = color C' (x, F.val[l]) := by
        apply fan_edges_invariant ha hj hC' hx (by omega) heq
      rw [← this]
      apply freeColors_inversion_invariant' hC' ?_ h
      apply color_neq_of_fan_edge ha hj hx (by omega) (by omega)
  · use ⟨j.val - 1, Nat.sub_lt_of_lt j.isLt⟩
    constructor
    · apply freeColor_of_not_exists_and_isSome _ ha
      apply not_exists_of_freeColor at aux1
      contrapose! aux1
      rcases aux1 with ⟨v, hv⟩
      use v
      rw [← hv]
      simp [isInverted, isInverted_notmem] at hC'
      rcases hC' with ⟨hC', _⟩
      apply hC'
      · rw [← mem_edgeSet_iff_present]
        apply C'.representsEdgesAx
        simp [color] at ⊢ hv
        rwa [hv]
      · rw [pathEdges, mem_allAdjacentPairs_iff_adjacent]
        by_contra hc
        apply mem_of_adjacent at hc
        tauto
    · have : j.val - 1 + 1 = j := by omega
      rw [this, colorAx]
      unfold fan_prop
      have : List.Chain' (fun f₁ f₂ ↦ color C (x, f₂) ∈ freeColorsOn C f₁) (F.val.extract 0 ↑j).toList := by
        have := F.colorAx
        unfold colorAx fan_prop at this
        simp_all
        exact List.Chain'.take this ↑j
      apply chain'_imp_of_mem _ this
      intro z hz w hw h
      simp at hz hw
      have : color C (x, w) = color C' (x, w) := by
        rcases List.getElem_of_mem hz with ⟨k, hk1, hk2⟩
        rcases List.getElem_of_mem hw with ⟨l, hl1, hl2⟩
        simp at hk1 hk2 hl1 hl2
        subst hk2 hl2
        apply fan_edges_invariant ha hj hC' hx (by omega) (by omega)
      rw [← this]
      apply freeColors_inversion_invariant' hC' ?_ h
      rcases List.getElem_of_mem hz with ⟨k, hk1, hk2⟩
      rcases List.getElem_of_mem hw with ⟨l, hl1, hl2⟩
      simp at hk1 hk2 hl1 hl2
      subst hk2 hl2
      apply color_neq_of_fan_edge ha hj hx (by omega) (by omega)

include ha hb in
theorem inversion_guarantee (F : Fan C x y)
  {C' : EdgeColoring c G} {P : Path C a b x}
  (hC' : isInverted C C' P) (ha1 : a ∈ freeColorsOn C (last F))
  (hF : isMaximal F) (hxy : color C (x, y) = none)
  (hx : b ∈ freeColorsOn C x) :
  ∃ i : Fin F.val.size, a ∈ freeColorsOn C' F.val[i] ∧ colorAx C' (Array.extract F.val 0 (i+1)) x := by
  have hsize : (F.val.size - 1 + 1) = F.val.size := by
    apply Nat.sub_add_cancel
    apply Nat.succ_le_of_lt
    exact Array.size_pos_iff.mpr F.nonemptyAx
  by_cases h : ∃ j : Fin F.val.size, color C (x, F.val[j]) = a
  apply inversion_guarantee_of_exists <;> assumption
  apply inversion_guarantee_of_not_exists <;> assumption

def findSubfanWithColor (F : Fan C x y)
  (C' : EdgeColoring c G)
  (P : Path C a b x)
  (h : isInverted C C' P) : Fan C' x y where
  val := takeUntil (a ∉ freeColorsOn C' ·) F.val
  nborsAx := by
    intro v hv
    apply F.nborsAx
    apply List.IsPrefix.mem hv
    rw [← List.isPrefixOf_iff_prefix, Array.isPrefixOf_toList]
    exact takeUntil_prefix (a ∉ freeColorsOn C' ·) F.val
  nonemptyAx := by
    simp [takeUntil]
    exact F.nonemptyAx
  firstElemAx := by
    simp [takeUntil]
    exact F.firstElemAx
  colorAx := by
    simp [colorAx]
    apply List.Chain'.prefix (l := F.val.toList)
    · unfold fan_prop

      -- Path inversion guarantee
      sorry
    · simp [← List.isPrefixOf_iff_prefix, Array.isPrefixOf_toList]
      apply takeUntil_prefix
  nodupAx := by
    apply List.Sublist.nodup ?_ F.nodupAx
    apply List.IsPrefix.sublist
    rw [← List.isPrefixOf_iff_prefix, Array.isPrefixOf_toList]
    exact takeUntil_prefix (a ∉ freeColorsOn C' ·) F.val

theorem subfan_spec (F : Fan C x y)
  (C' : EdgeColoring c G)
  (P : Path C a b x)
  (h : isInverted C C' P)
  (h2 : a ∈ freeColorsOn C (last F)) :
  a ∈ freeColorsOn C' (last (findSubfanWithColor C F C' P h)) := by
  simp [last]
  by_cases hF : (findSubfanWithColor C F C' P h).val = F.val
  simp_rw [hF]


  sorry

  simp [findSubfanWithColor]



  sorry
