import Vizing.Path.PathEdges


set_option maxHeartbeats 1000000

namespace Path
open Graph
open EdgeColoring
open Aux

variable {n c : Nat} {G : Graph n} {C : EdgeColoring c G}
  {a b : Color c} (ha : a.isSome) (hb : b.isSome)

include ha hb in
theorem edges_present (L : List (Vertex n))
  (colorAx : alternatesColor C L a b) : List.Chain' (fun v₁ v₂ ↦ present G (v₁, v₂)) L := by
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

theorem uncolor_spec1 (L : List (Vertex n)) (hnodup : L.Nodup) (hcolor : alternatesColor C L a b):
  ∀ e, e ∉ allAdjacentPairs L → color C e = color (uncolor C a b ha hb L hnodup hcolor) e := by
  fun_induction uncolor <;> simp_all [allAdjacentPairs]
  rename_i hnodup _ _ ih
  intro u v h1 h2 h3
  rw [← ih]
  apply color_invariant
  simp; tauto
  assumption

theorem uncolor_spec2 (L : List (Vertex n)) (hnodup : L.Nodup) (hcolor : alternatesColor C L a b):
  ∀ e, e ∈ allAdjacentPairs L → color (uncolor C a b ha hb L hnodup hcolor) e = none := by
  fun_induction uncolor <;> simp_all [allAdjacentPairs]
  rename_i hnodup _ _ ih
  rw [color_symm]; simp
  rw [← uncolor_spec1]
  rw [color_symm]
  apply setEdgeColor_spec
  intro hc
  rw [mem_allAdjacentPairs_iff_adjacent] at hc
  apply mem_of_adjacent at hc
  simp at hnodup hc
  tauto

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

theorem recolor_spec1 (hne : a ≠ b)
  (L : List (Vertex n)) (hnodup : L.Nodup)
  (h1 : List.Chain' (fun e₁ e₂ ↦ present G (e₁, e₂)) L)
  (h2 : ∀ v ∈ L.tail, a ∈ freeColorsOn C v)
  (h3 : ∀ v ∈ L, b ∈ freeColorsOn C v) :
  ∀ e, e ∉ allAdjacentPairs L → color C e = color (recolor C a b ha hb hne L hnodup h1 h2 h3) e := by
  fun_induction recolor <;> simp_all [allAdjacentPairs]
  rename_i ih
  intro a b h4 h5 h6
  rw [← ih]
  apply color_invariant
  simp_all
  assumption

theorem recolor_spec2 (hne : a ≠ b)
  (L : List (Vertex n)) (hnodup : L.Nodup)
  (h1 : List.Chain' (fun e₁ e₂ ↦ present G (e₁, e₂)) L)
  (h2 : ∀ v ∈ L.tail, a ∈ freeColorsOn C v)
  (h3 : ∀ v ∈ L, b ∈ freeColorsOn C v) :
  alternatesColor (recolor C a b ha hb hne L hnodup h1 h2 h3) L b a := by
  unfold alternatesColor
  fun_induction recolor <;> simp [alternates]
  constructor
  rename_i hnodup _ _ _ _ _ _ _ _
  rw [← recolor_spec1]
  apply setEdgeColor_spec
  · intro hc
    rw [mem_allAdjacentPairs_iff_adjacent] at hc
    apply mem_of_adjacent at hc
    simp at hnodup hc
    tauto
  assumption

-- theorem recolor_spec3 (hne : a ≠ b)
--   (L : List (Vertex n)) (hnodup : L.Nodup) (hl : L ≠ [])
--   (h1 : List.Chain' (fun e₁ e₂ ↦ present G (e₁, e₂)) L)
--   (h2 : ∀ v ∈ L.tail, a ∈ freeColorsOn C v)
--   (h3 : ∀ v ∈ L, b ∈ freeColorsOn C v)
--   (h4 : next a b L ∈ freeColorsOn C (L.getLast hl)) :
--   next b a L ∈ freeColorsOn (recolor C a b ha hb hne L hnodup h1 h2 h3) (L.getLast hl) := by
--   fun_induction recolor
--   · contradiction
--   · simp_all [next]
--   · rename_i p₁ p₂ ps hnodup _ _ _ _ _ _ _ ih
--     simp_all!
--     by_cases hps : ps = []
--     · subst hps
--       simp_all [next, recolor]
--     · apply ih
--       rwa [← freeColors_invariant]
--       simp_all!
--       grind

variable
  {x : Vertex n}
  (hne : a ≠ b)
  (hfree : b ∈ freeColorsOn C x)

def invert {P : Path C a b x} (h : isMaximalPath P) : EdgeColoring c G :=
  recolor (uncolor C a b ha hb P.val P.nodupAx P.colorAx)
    a b ha hb hne P.val P.nodupAx (edges_present ha hb P.val P.colorAx)
    (by
    intro v hv
    apply a_free_of_uncolored
    · rwa [List.head_eq_getElem, P.firstElemAx]
      exact P.nonemptyAx
    · apply h
    · exact List.mem_of_mem_tail hv)
    (by
    intro v hv
    apply b_free_of_uncolored
    · rwa [List.head_eq_getElem, P.firstElemAx]
      exact P.nonemptyAx
    · apply h
    · assumption)


def isInverted_notmem (C C' : EdgeColoring c G) (P : Path C a b x) : Prop :=
  ∀ e, e ∉ pathEdges P → (color C e = color C' e)

def isInverted_mem (C C' : EdgeColoring c G) (P : Path C a b x) : Prop :=
  ∀ e ∈ pathEdges P, (color C e = a ↔ color C' e = b) ∧ (color C e = b ↔ color C' e = a)

def isInverted (C C' : EdgeColoring c G) (P : Path C a b x) :=
  isInverted_notmem C C' P ∧ isInverted_mem C C' P

theorem invert_spec_aux (C C' : EdgeColoring c G) (L : List (Vertex n))
  (h1 : alternatesColor C L a b) (h2 : alternatesColor C' L b a) :
  ∀ e ∈ allAdjacentPairs L, (color C e = a ↔ color C' e = b) ∧ (color C e = b ↔ color C' e = a) := by
  intro e he
  fun_induction allAdjacentPairs generalizing a b <;> simp_all
  rename_i x₁ x₂ xs ih
  unfold alternatesColor alternates at h1 h2
  rcases he with he | he | he
  · subst he
    simp_all [eq_comm]
  · subst he
    simp_all [color_symm, eq_comm]
  · apply And.comm.mp
    apply @ih b a
    · rw [alternatesColor]; exact alternates_tail h1
    · rw [alternatesColor]; exact alternates_tail h2
    · assumption

theorem invert_spec {P : Path C a b x} (h : isMaximalPath P) :
  isInverted C (invert ha hb hne hfree h) P := by
  constructor <;> intro e he
  rw [invert, ← recolor_spec1, ← uncolor_spec1]
  any_goals simpa [pathEdges] using he
  apply invert_spec_aux
  · exact P.colorAx
  · rw [invert]; apply recolor_spec2
  simpa [pathEdges] using he

theorem inversion_invariant_of_edgeColor {C C' : EdgeColoring c G} {P : Path C a b x} {e : Edge n}
  (h1 : isInverted C C' P) (h2 : color C e ≠ a ∧ color C e ≠ b) :
  color C e = color C' e := by
  apply h1.left
  contrapose! h2
  exact color_of_mem_pathEdges h2

theorem inversion_invariant_of_edgeColor' {C C' : EdgeColoring c G} {P : Path C a b x} {e : Edge n}
  (h1 : isInverted C C' P) (h2 : color C' e ≠ a ∧ color C' e ≠ b) :
  color C e = color C' e := by
  apply h1.left
  contrapose! h2
  have := color_of_mem_pathEdges h2
  apply h1.right at h2
  tauto

def invertedPath {P : Path C a b x} (h : isMaximalPath P) : Path (invert ha hb hne hfree h) b a x where
  val := P.val
  nonemptyAx := P.nonemptyAx
  firstElemAx := P.firstElemAx
  nodupAx := P.nodupAx
  colorAx := by
    rw [invert]
    apply recolor_spec2

include ha hb hfree in
theorem mem_path_of_color' {C' : EdgeColoring c G} {P : Path C a b x} (hc : isInverted C C' P)
  {u v : Vertex n} (h : u ∈ P.val) (h2 : color C' (u, v) = a ∨ color C' (u, v) = b)
  (h3 : isMaximalPath P) :
  (u, v) ∈ pathEdges P := by
  apply mem_path_of_color_aux ha hb hfree P.nonemptyAx P.firstElemAx P.colorAx h3 h
  rcases hc with ⟨hc1, hc2⟩
  by_cases h : (u, v) ∈ pathEdges P
  · specialize hc2 (u, v) h
    tauto
  · specialize hc1 (u, v) h
    simp_all

include ha hb hfree in
theorem freeColor_inv_a {C' : EdgeColoring c G} {P : Path C a b x}
  (hc : isInverted C C' P) (h : isMaximalPath P) {u : Vertex n}
  (h1 : u ∈ P.val) (h2 : a ∈ freeColorsOn C u) :
  b ∈ freeColorsOn C' u := by
  apply not_exists_of_freeColor at h2
  apply freeColor_of_not_exists_and_isSome _ hb
  contrapose! h2
  rcases h2 with ⟨v, hv⟩
  use v
  have : (u, v) ∈ pathEdges P := by
    apply mem_path_of_color' ha hb hfree hc h1 (by tauto) h
  have := hc.right (u, v) (mem_path_of_color' ha hb hfree hc h1 (by tauto) h)
  tauto

include ha hb hfree in
theorem freeColor_inv_b {C' : EdgeColoring c G} {P : Path C a b x}
  (hc : isInverted C C' P) (h : isMaximalPath P) {u : Vertex n}
  (h1 : u ∈ P.val) (h2 : b ∈ freeColorsOn C u) :
  a ∈ freeColorsOn C' u := by
  apply not_exists_of_freeColor at h2
  apply freeColor_of_not_exists_and_isSome _ ha
  contrapose! h2
  rcases h2 with ⟨v, hv⟩
  use v
  have : (u, v) ∈ pathEdges P := by
    apply mem_path_of_color' ha hb hfree hc h1 (by tauto) h
  have := hc.right (u, v) (mem_path_of_color' ha hb hfree hc h1 (by tauto) h)
  tauto

-- theorem freeColor_head_inv {P : Path C a b x} (h : isMaximalPath P) :
--   a ∈ freeColorsOn (invert ha hb hne hfree h) x := by
--   have hcolor := P.colorAx
--   unfold alternatesColor alternates at hcolor
--   split at hcolor
--   · simp_all [P.nonemptyAx]
--   · have aux : P.val = [x] := by
--       have := P.firstElemAx
--       simp_all
--     simpa [invert, uncolor, recolor, isMaximalPath, next, aux] using h
--   · rename_i _ v₁ v₂ vs heq
--     have hx : x = v₁ := by
--       have := P.firstElemAx
--       simp_all
--     have : (x, v₂) ∈ pathEdges P := by
--       rw [pathEdges, mem_allAdjacentPairs_iff_adjacent]
--       left
--       use 0, (by simp_all)
--       simp_all
--     apply freeColor_of_not_exists_and_isSome _ ha
--     intro hc
--     rcases hc with ⟨v, hv⟩
--     by_cases h' : (x, v) ∈ pathEdges P
--     · have := (invert_spec ha hb hne hfree h).right (x, v) h'
--       simp [hv, hne] at this
--       apply not_exists_of_freeColor at hfree
--       simp_all
--     · have := (invert_spec ha hb hne hfree h).left (x, v) h'
--       subst hx
--       rw [hv] at this
--       rw [← this] at ha
--       rw [← hcolor.left] at this
--       apply color_unique at this
--       simp_all [Option.isSome_iff_ne_none]

-- theorem inv_maximal_of_maximal {P : Path C a b x} (h : isMaximalPath P) :
--   isMaximalPath (invertedPath ha hb hne hfree h) := by
--     simp [isMaximalPath, invertedPath] at h ⊢
--     unfold invert
--     apply recolor_spec3
--     rcases next_eq_a_or_b a b P.val with hnext | hnext <;> rw [hnext]
--     · apply a_free_of_uncolored
--       rwa [List.head_eq_getElem, P.firstElemAx]
--       exact P.nonemptyAx
--       assumption
--       simp
--     · apply b_free_of_uncolored
--       rwa [List.head_eq_getElem, P.firstElemAx]
--       exact P.nonemptyAx
--       assumption
--       simp
