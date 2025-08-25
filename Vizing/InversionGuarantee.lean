import Vizing.Aux
import Vizing.Graph
import Vizing.EdgeColoring
import Vizing.Fan
import Vizing.Path

open Aux Graph EdgeColoring Fan Path

variable
  {n c : Nat} {G : Graph n} (C : EdgeColoring c G)
  {x y : Vertex n} {a b : Color c} (ha : a.isSome)

-- Maximality : all free colors on last vertex of fan are free on x

include ha in
theorem inversion_guarantee (F : Fan C x y)
  {C' : EdgeColoring c G}
  {P : Path C a b x}
  (hC' : isInverted C C' P)
  (ha1 : a ∈ freeColorsOn C (last F))
  (hF : isMaximal F)
  (hxy : color C (x, y) = none) :
  ∃ i : Fin F.val.size, a ∈ freeColorsOn C' F.val[i] := by
  by_cases h : ∃ j : Fin F.val.size, color C (x, F.val[j]) = a
  rcases h with ⟨j, hj⟩
  have aux0 : j.val > 0 := by
    by_contra hc
    simp at hc
    simp_all [F.firstElemAx, Option.isSome_iff_ne_none]
  have aux1 : a ∈ freeColorsOn C F.val[j.val - 1] := by
    rw [← hj]
    have := F.colorAx
    apply chain'_rel_of_idx_consec (Nat.sub_lt_of_lt j.isLt) (j.isLt) F.colorAx
    omega
  by_cases hp : F.val[j.val - 1] ∈ P.val
  · use ⟨F.val.size - 1, (by simp; apply Array.size_pos_iff.mpr; exact F.nonemptyAx)⟩
    apply freeColor_of_not_exists_and_isSome _ ha
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
      simp [last, Array.back] at ha1
      simp [isMaximal] at hF
      apply mem_pathEdges_if at hc
      simp at hc
      have : F.val[F.val.size - 1] ≠ F.val[j.val - 1] := by
        by_contra hc
        apply (List.Nodup.getElem_inj_iff F.nodupAx).mp at hc
        have : j = F.val.size := by omega
        have := j.isLt
        omega
      have := isLast_if C hp aux1
      have := isLast_if C hc.left ha1
      simp_all
  · use ⟨j.val - 1, Nat.sub_lt_of_lt j.isLt⟩
    apply freeColor_of_not_exists_and_isSome _ ha
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
    · apply not_mem_pathEdges_if
      left
      trivial
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
    · contrapose! h
      simp [color]
      rw [← hi2]
      rcases Array.mem_iff_getElem.mp h with ⟨j, hj1, hj2⟩
      apply Fin.exists_iff.mpr
      use j, hj1
      simp [hj2]
  have aux1 : P.val = [x] := by
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
  use ⟨F.val.size - 1, (by simp; apply Array.size_pos_iff.mpr; exact F.nonemptyAx)⟩
  apply freeColor_of_not_exists_and_isSome _ ha
  simp [isInverted, isInverted_notmem, isInverted_mem, aux1, pathEdges, color] at hC'
  apply not_exists_of_freeColor at ha1
  contrapose! ha1
  rcases ha1 with ⟨v, hv⟩
  use v
  rw [← hv]
  simp [color, last, Array.back_eq_getElem]
  apply hC'
  rw [← mem_edgeSet_iff_present]
  apply C'.representsEdgesAx
  simp [color] at ⊢ hv
  rwa [hv]

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
