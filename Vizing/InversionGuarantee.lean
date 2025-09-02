import Vizing.Aux
import Vizing.Graph
import Vizing.EdgeColoring
import Vizing.Fan
import Vizing.Path

open Aux Graph EdgeColoring Fan Path

variable
  {n c : Nat} {G : Graph n} (C : EdgeColoring c G)
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
      rw [← mem_edgeSet_iff_present]
      apply C'.representsEdgesAx
      rwa [← color.eq_def, hv]
      assumption


theorem colorAx_invariant
  {C' : EdgeColoring c G} {F : List (Vertex n)} (hF : F ≠ [])
  (hF2 : F.Nodup)
  (h1 : ∀ (a b : Vertex n), (a, b) ∈ (toEdgeSet G).val → color C (a, b) = color C' (a, b))
  (h2 : List.Chain' (fun f₁ f₂ ↦ color C (x, f₂) ∈ freeColorsOn C f₁) F)
  (h3 : ∀ z ∈ F, z ≠ F.head hF → (color C (x, z)).isSome) :
  List.Chain' (fun f₁ f₂ ↦ color C' (x, f₂) ∈ freeColorsOn C' f₁) F := by
  induction' F
  · trivial
  · rename_i head tail ih
    apply List.Chain'.cons'
    by_cases htail : tail = []
    · subst htail
      trivial
    apply ih
    · exact List.Nodup.of_cons hF2
    · apply List.Chain'.tail at h2
      simpa using h2
    · intro z hz1 hz2
      have := List.mem_cons_of_mem head hz1
      apply h3
      · exact this
      · simp only [List.head_cons]
        by_contra hc
        rw [hc] at hz1
        exact List.Nodup.notMem hF2 hz1
    · assumption
    · intro z hz
      have aux : (x, z) ∈ (toEdgeSet G).val := by
        rw [← mem_edgeSet_iff_present]
        apply C.representsEdgesAx
        apply h3
        · exact List.mem_cons_of_mem head (List.mem_of_mem_head? hz)
        · grind
      rcases List.chain'_cons'.mp h2 with ⟨h4, _⟩
      specialize h4 z hz
      have : ∀ a, a ∈ freeColorsOn C head → a ∈ freeColorsOn C' head := by
        intro a ha
        have h5 : a.isSome := by exact isSome_if_mem_freeColorsOn C head ha
        apply freeColor_of_not_exists_and_isSome
        · assumption
        apply not_exists_of_freeColor at ha
        contrapose! ha
        rcases ha with ⟨v, hv⟩
        use v
        rwa [h1]
        · rw [← mem_edgeSet_iff_present]
          apply C'.representsEdgesAx
          rwa [← color.eq_def, hv]
      rw [← h1]
      tauto
      assumption

include ha in
theorem inversion_guarantee (F : Fan C x y)
  {C' : EdgeColoring c G} {P : Path C a b x}
  (hC' : isInverted C C' P) (ha1 : a ∈ freeColorsOn C (last F))
  (hF : isMaximal F) (hxy : color C (x, y) = none) :
  ∃ i : Fin F.val.size, a ∈ freeColorsOn C' F.val[i] ∧ colorAx C' (Array.extract F.val 0 (i+1)) x := by
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
    ·
      sorry
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
      · apply not_mem_pathEdges_if
        left
        trivial
    · sorry
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
  simp [isInverted, isInverted_notmem, isInverted_mem, aux1, pathEdges, color] at hC'
  constructor
  · apply freeColor_of_not_exists_and_isSome _ ha
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
  · have hcolor := F.colorAx
    have : (F.val.size - 1 + 1) = F.val.size := by
      apply Nat.sub_add_cancel
      apply Nat.succ_le_of_lt
      exact Array.size_pos_iff.mpr F.nonemptyAx
    simp [this]
    unfold colorAx fan_prop color at ⊢ hcolor
    -- simp at ⊢ hcolor
    simp_all
    induction' F.val.toList
    · trivial
    · rename_i head tail ih
      apply List.Chain'.cons' ih
      intro z hz
      rw [← hC']
      · sorry
      · rw [← mem_edgeSet_iff_present]
        apply C.representsEdgesAx
        simp
        apply fan_colored_edges x y F
        stop




    -- Lemma : inverted path : freeColorsOn remain the same for everything except first and last ..?



        sorry

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
