import Vizing.Path.Defs

namespace Path
open Graph
open EdgeColoring
open Aux

variable {n c : Nat} {G : Graph n} {C : EdgeColoring c G}
  {a b : Color c} (ha : a.isSome) (hb : b.isSome)

include ha hb in
theorem edges_present (L : List (Vertex n))
  (colorAx : alternatesColor C L a b) : List.Chain' (fun e₁ e₂ ↦ present G (e₁, e₂)) L := by
  rw [alternatesColor] at colorAx
  induction' L with head tail ih generalizing a b
  trivial
  by_cases htail : tail = []
  · simp [htail]
  rcases List.exists_cons_of_ne_nil htail with ⟨v, vs, h⟩
  subst h
  rw [alternates.eq_def] at colorAx
  simp at colorAx
  apply List.Chain'.cons_of_ne_nil htail
  · apply @ih b a hb ha colorAx.right
  apply C.representsEdgesAx
  simp [color] at ⊢ colorAx
  rwa [colorAx.left]

def setColor_preserves_alternatesColor {C : EdgeColoring c G} {L : List (Vertex n)} (hcolor : alternatesColor C L a b)
  (d : Color c) (v₁ v₂ : Vertex n) (h : v₁ ∉ L ∨ v₂ ∉ L) (hpres : present G (v₁, v₂))
  (hvalid : edgeColorValid C (v₁, v₂) d):
    alternatesColor (setEdgeColor C (v₁, v₂) d hpres hvalid) L a b := by
  rw [alternatesColor] at ⊢ hcolor
  fun_induction alternates _ a b L <;> simp_all!
  rename_i a b v₁ v₂ vs ih
  constructor
  rw [← color_invariant]
  · exact hcolor.left
  · simp; tauto
  · apply ih; tauto

def uncolor (C : EdgeColoring c G) (a b : Color c) (ha : a.isSome) (hb : b.isSome)
  (L : List (Vertex n)) (hnodup : L.Nodup) (h : alternatesColor C L a b) : EdgeColoring c G :=
  match hl : L with
  | [] => C
  | [_] => C
  | p₁ :: p₂ :: ps =>
    have hpres : present G (p₁, p₂) := by
      subst hl
      apply edges_present ha hb at h
      simp at h
      exact h.left
    uncolor (setEdgeColor C (p₁, p₂) none hpres
    (by simp [edgeColorValid]))
      b a hb ha (p₂ :: ps) (List.Nodup.of_cons hnodup) (by
        apply setColor_preserves_alternatesColor hb ha
        · rw [alternatesColor] at h ⊢
          apply alternates_tail at h
          assumption
        · simp at ⊢ hnodup
          tauto)

-- def uncolor {x : Vertex n} (P : Path C a b x) := uncolor C a b ha hb P.val P.nodupAx P.colorAx

-- If maximal is singleton, then both colors free on it

theorem mem_freeColors_uncolor {a b d : Color c} {C : EdgeColoring c G}
  {ha : a.isSome} {hb : b.isSome} {L : List (Vertex n)} {hnodup : L.Nodup} {hcolor : alternatesColor C L a b}
  {v : Vertex n}
  (h : d ∈ freeColorsOn C v) :
  d ∈ freeColorsOn (uncolor C a b ha hb L hnodup hcolor) v := by
  fun_induction uncolor
  any_goals simp_all
  rename_i C a b ha hb p₁ p₂ ps hnodup hcolor hpres ih
  apply ih
  apply color_free_if
  assumption
  simp [freeColorsOn, allColors] at h
  rcases h with ⟨h, _⟩
  by_contra hc; subst hc; simp at h

theorem free_colors_of_uncolored {L : List (Vertex n)}
  (hne : L ≠ [])
  (hfirst : b ∈ freeColorsOn C (L.head hne))
  (hlast : next a b L ∈ freeColorsOn C (L.getLast hne))
  (hnodup : L.Nodup) (h : alternatesColor C L a b) :
  ∀ v ∈ L, a ∈ freeColorsOn (uncolor C a b ha hb L hnodup h) v ∧
           b ∈ freeColorsOn (uncolor C a b ha hb L hnodup h) v:= by
  intro v hv
  fun_induction uncolor <;> simp_all!
  rename_i C a b ha hb p₁ p₂ ps _ h _ ih
  rcases hv with hv | hv
  subst hv
  constructor
  · apply mem_freeColors_uncolor
    unfold alternatesColor alternates at h
    rw [← h.left] at ⊢ ha
    apply (setEdgeColor_freeOn _ _ _ _ _ _).left
    assumption
  · apply mem_freeColors_uncolor
    apply color_free_if
    assumption
    exact Ne.symm (Option.ne_none_iff_isSome.mpr hb)
  rw [And.comm]
  apply ih
  unfold alternatesColor alternates at h
  rw [← h.left] at ⊢ ha
  apply (setEdgeColor_freeOn _ _ _ _ _ _).right
  assumption
  apply color_free_if
  assumption
  rcases next_eq_a_or_b a b ps with hnext | hnext
  any_goals rw [hnext]; exact Ne.symm (Option.ne_none_iff_isSome.mpr (by assumption))
  assumption

theorem a_free_of_uncolored {L : List (Vertex n)}
  (hne : L ≠ [])
  (hfirst : b ∈ freeColorsOn C (L.head hne))
  (hlast : next a b L ∈ freeColorsOn C (L.getLast hne))
  (hnodup : L.Nodup) (h : alternatesColor C L a b) :
  ∀ v ∈ L, a ∈ freeColorsOn (uncolor C a b ha hb L hnodup h) v := by
  exact fun v x ↦ (free_colors_of_uncolored ha hb hne hfirst hlast hnodup h v x).left

theorem b_free_of_uncolored {L : List (Vertex n)}
  (hne : L ≠ [])
  (hfirst : b ∈ freeColorsOn C (L.head hne))
  (hlast : next a b L ∈ freeColorsOn C (L.getLast hne))
  (hnodup : L.Nodup) (h : alternatesColor C L a b) :
  ∀ v ∈ L, b ∈ freeColorsOn (uncolor C a b ha hb L hnodup h) v := by
  exact fun v x ↦ (free_colors_of_uncolored ha hb hne hfirst hlast hnodup h v x).right

def recolor (C : EdgeColoring c G) (a b : Color c) (ha : a.isSome) (hb : b.isSome)
  (hne : a ≠ b)
  (L : List (Vertex n)) (hnodup : L.Nodup)
  (h1 : List.Chain' (fun e₁ e₂ ↦ present G (e₁, e₂)) L)
  (h2 : ∀ v ∈ L.tail, a ∈ freeColorsOn C v)
  (h3 : ∀ v ∈ L, b ∈ freeColorsOn C v)
  : EdgeColoring c G :=
  match hl : L with
  | [] => C
  | [_] => C
  | p₁ :: p₂ :: ps =>
    have hpres : present G (p₁, p₂) := by
      simp at h1
      exact h1.left
    have hvalid : edgeColorValid C (p₁, p₂) b := by
      simp [edgeColorValid]
      right
      exact ⟨h3 p₁ (by tauto), h3 p₂ (by tauto)⟩
    have auxa : ∀ v ∈ p₂ :: ps,
      a ∈ freeColorsOn (setEdgeColor C (p₁, p₂) b hpres hvalid) v := by
      intro v hv
      apply color_free_if
      · apply h2; simpa using hv
      exact Ne.symm hne
    have auxb : ∀ v ∈ (p₂ :: ps).tail,
      b ∈ freeColorsOn (setEdgeColor C (p₁, p₂) b hpres hvalid) v := by
      simp
      intro v hv
      rw [← freeColors_invariant]
      · apply h3; simp [hv]
      · simp at ⊢ hnodup
        contrapose! hv
        rcases hv with hv | hv <;> (subst hv; tauto)
    recolor (setEdgeColor C (p₁, p₂) b hpres hvalid)
      b a hb ha (Ne.symm hne) (p₂ :: ps) (by simp at ⊢ hnodup; tauto)
      (by apply List.Chain'.tail at h1; simpa using h1)
      auxb auxa

variable
  {x : Vertex n}
  (hne : a ≠ b)
  (hfree : b ∈ freeColorsOn C x)

def invert : EdgeColoring c G :=
  let P := maximalPath C ha hb hne hfree
  recolor (uncolor C a b ha hb P.val P.nodupAx P.colorAx)
    a b ha hb hne P.val P.nodupAx (edges_present ha hb P.val P.colorAx)
    (by
    intro v h
    apply a_free_of_uncolored
    · rwa [List.head_eq_getElem, P.firstElemAx]
      exact P.nonemptyAx
    · apply maximalPath_isMaximal
    · exact List.mem_of_mem_tail h)
    (by
    intro v h
    apply b_free_of_uncolored
    · rwa [List.head_eq_getElem, P.firstElemAx]
      exact P.nonemptyAx
    · apply maximalPath_isMaximal
    · assumption)
