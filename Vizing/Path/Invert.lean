import Vizing.Path.PathEdges

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


-- def pathEdges (P : Path C a b x) : EdgeSet G where
--   val :=

-- def pathEdges (P : List (Vertex n)) : List (Edge n) :=
--   match P with
-- | [] => []
-- | [_] => []
-- | p₁ :: p₂ :: ps => (p₁, p₂) :: (p₂, p₁) :: pathEdges (p₂ :: ps)

-- theorem pathEdges_spec (P : List (Vertex n)) :
--   List.Chain' (fun u v ↦ (u, v) ∈ pathEdges P) P := by
--   fun_induction pathEdges
--   all_goals simp_all
--   simp_all [List.chain'_iff_get]

-- theorem not_mem_pathEdges_if_aux {e : Edge n} {P : List (Vertex n)}
--   (h : e.1 ∉ P ∨ e.2 ∉ P) :
--   e ∉ pathEdges P := by
--   rcases h with h | h
--   all_goals
--   fun_induction pathEdges P <;> simp_all
--   contrapose! h
--   rcases h with h | h <;> simp_all

-- theorem not_mem_pathEdges_if {e : Edge n} {P : Path C a b x}
--   (h : e.1 ∉ P.val ∨ e.2 ∉ P.val) :
--   e ∉ pathEdges P.val := not_mem_pathEdges_if_aux h

-- theorem mem_pathEdges_if {e : Edge n} {P : Path C a b x}
--   (h : e ∈ pathEdges P.val) : e.1 ∈ P.val ∧ e.2 ∈ P.val := by
--   contrapose! h
--   exact not_mem_pathEdges_if h

-- theorem mem_pathEdges_symm {e : Edge n} {P : List (Vertex n)}
--   (h : e ∈ pathEdges P) : e.swap ∈ pathEdges P := by
--   fun_induction pathEdges P <;> simp_all
--   rcases h with h | h | h
--   any_goals subst h
--   all_goals tauto

-- include hne in
-- theorem exists_other_nbor_of_mem_pathEdges {u v : Vertex n} {P : (List (Vertex n))}
--   (h : (u, v) ∈ pathEdges P) (hne : P ≠ []) (hu : u ≠ P.head hne ∧ u ≠ P.getLast hne)
--   (hcolor : alternatesColor C P a b) :
--   ∃ w, (u, w) ∈ pathEdges P ∧ color C (u, w) ≠ color C (u, v) := by
--   fun_induction pathEdges P <;> simp_all
--   unfold alternatesColor alternates alternates at hcolor
--   split at hcolor <;> simp_all [pathEdges]
--   rename_i heq
--   rcases h with h | h
--   simp_all [color_symm]
--   left
--   tauto
--   rename_i p₁ p₂ ps _ v₁ v₂ vs
--   rcases h with h | h | h
--   use p₁
--   constructor
--   · left
--     tauto
--   · simp_all [color_symm]
--   use v
--   constructor
--   · tauto
--   -- · simp_all [color_symm]
--     -- have : u ∈ (v₂ :: vs) ∧ v ∈ (v₂ :: vs) := by
--     --   have := @not_mem_pathEdges_if_aux _ (u, v) (v₂ :: vs)
--     --   simp at this


--       -- stop







--   stop










--   sorry



-- -- theorem getElem_of_mem_pathEdges {v : Vertex n} {P : List (Vertex n)}
-- --   {i : Nat} {hi : i < P.length}
-- --   (h : (P[i], v) ∈ pathEdges P) :
-- --   P[i+1]? = some v ∨ P[i-1]? = some v := by
-- --   fun_induction pathEdges P <;> simp_all
-- --   rename_i p₁ p₂ ps ih
-- --   rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
-- --   subst h2




-- --   sorry

-- #check List.getElem_of_mem

-- include ha hb in
-- theorem present_of_mem_pathEdges {e : Edge n} {P : List (Vertex n)}
--   (h1 : alternatesColor C P a b) (h2 : e ∈ pathEdges P) :
--   present G e := by
--   have := edges_present ha hb P h1
--   have := pathEdges_spec P




--   sorry

-- theorem getElem_of_mem_pathEdges {u v : Vertex n} {P : List (Vertex n)}
--   (h : (u, v) ∈ pathEdges P) (h2 : P.Nodup) :
--   (∃ i, ∃ (h : i < P.length - 1), P[i] = u ∧ P[i + 1] = v) ∨
--   (∃ i, ∃ (h : i < P.length), P[i] = u ∧ P[i-1] = v) := by
--   fun_induction pathEdges
--   · simp_all
--   · simp_all
--   rename_i p₁ p₂ ps ih
--   simp at h
--   rcases h with h | h | h
--   · left
--     use 0, (by simp_all)
--     simp [h]
--   · right
--     use 1, (by simp_all)
--     simp [h]
--   · specialize ih h (List.Nodup.of_cons h2)
--     rcases ih with ⟨i, hi, ih⟩ | ⟨i, hi, ih⟩
--     · left
--       use i+1, (by simpa)
--       simpa
--     · right
--       use i+1, (by simpa)
--       simp [ih]
--       rw [List.getElem_cons]
--       split
--       have : u ∈ (p₂ :: ps) ∧ v ∈ (p₂ :: ps) := by
--         have := @not_mem_pathEdges_if_aux _ (u, v) (p₂ :: ps)
--         simp_all
--         tauto
--       have : p₁ ≠ p₂ := by
--         simp at h2
--         tauto
--       have : p₁ ∉ (p₂ :: ps) := by
--         exact List.Nodup.notMem h2
--       have : p₂ ∉ ps := by
--         apply List.Nodup.notMem
--         exact List.Nodup.of_cons h2
--       simp_all
--       rcases ih with ⟨aux1, aux2⟩
--       subst aux1 aux2
--       exfalso
--       sorry
--       sorry










--   -- sorry

-- theorem color_of_mem_pathEdges {e : Edge n} {P : List (Vertex n)}
--   (h : e ∈ pathEdges P)
--   (hcolor : alternatesColor C P a b) :
--   color C e = a ∨ color C e = b := by
--   fun_induction pathEdges P generalizing a b <;> simp_all
--   unfold alternatesColor alternates at hcolor
--   rcases h with h | h | h <;> simp_all [color_symm]
--   rename_i ih
--   specialize @ih b a
--   apply Or.symm
--   apply ih
--   simp [alternatesColor]
--   tauto

def isInverted_notmem (C C' : EdgeColoring c G) (P : Path C a b x) : Prop :=
  ∀ e ∈ (toEdgeSet G).val, e ∉ pathEdges P → (color C e = color C' e)

def isInverted_mem (C C' : EdgeColoring c G) (P : Path C a b x) : Prop :=
  ∀ e ∈ pathEdges P, (color C e = a → color C' e = b) ∧ (color C e = b → color C' e = a)

def isInverted (C C' : EdgeColoring c G) (P : Path C a b x) :=
  isInverted_notmem C C' P ∧ isInverted_mem C C' P

theorem invert_spec : isInverted C (invert ha hb hne hfree) (maximalPath C ha hb hne hfree) := by sorry
