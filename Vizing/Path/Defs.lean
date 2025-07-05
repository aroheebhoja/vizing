import Vizing.EdgeColoring

set_option linter.dupNamespace false
set_option push_neg.use_distrib true
set_option maxHeartbeats 10000000

namespace Path
open Graph
open EdgeColoring
open Aux

variable {c n : Nat} {G : Graph n} (C : EdgeColoring c G)

/-
Let c and d be colors. A cdX-path is an edge path that goes through vertex X,
only contains edges colored c or d, and is maximal.
(We cannot add any other edge with color c or d to the path.)
If neither c nor d is incident on X, there is no such path.
If such a path exists, it is unique as at most one edge of each color can be
incident on X.
-/


/-

Path : List of vertices in order, all edges between 2 adjacent vertices only
colored c or d, no duplicates

-/


section

variable {n c : Nat} {G : Graph n} (C : EdgeColoring c G)
  (l : List (Vertex n)) (hl : l.Nodup)
  (a b : Color c) (hab : a.isSome ∧ b.isSome)

def colorPred :=
  l.Chain' (fun v₁ v₂ ↦ color C (v₁, v₂) = a ∨ color C (v₁, v₂) = b)

def alternatesColor : Prop :=
  aux a b l ∨ aux b a l where
@[simp]
aux (a b : Color c) : List (Vertex n) → Prop
  | v₁ :: (v₂ :: vs) => color C (v₁, v₂) = a ∧ aux b a (v₂ :: vs)
  | _ => true

include hl hab in
theorem alternatesColor_of_colorPred :
  colorPred C l a b → alternatesColor C l a b := by
  simp only [alternatesColor, colorPred]
  intro h
  induction' l with head tail ih
  · simp
  · unfold alternatesColor.aux
    split <;> simp_all
    rename_i v₁ v₂ vs hv
    rcases hv with ⟨hv1, hv2⟩
    subst hv2
    rcases h with ⟨h1, h2⟩
    cases vs
    · simpa
    · rename_i vs v₃ rest
      have := color_unique C v₂ v₁ v₃
      have aux1 : color C (v₁, v₂) ≠ none := by
        apply Option.isSome_iff_ne_none.mp
        rcases h1 with h1 | h1
        all_goals subst h1; tauto
      have aux2 : v₁ ≠ v₃ := by
        by_contra h; subst h
        rcases hl with ⟨⟨_, hc⟩, _, _⟩
        exact hc (List.mem_cons_self)
      simp_rw [Option.isSome_iff_ne_none] at hab
      rcases ih with ih | ih
      all_goals rw [color_symm, ih.left] at this; simp_all

include hl hab in
theorem colorPred_of_alternatesColor :
  alternatesColor C l a b → colorPred C l a b := by
  simp only [alternatesColor, colorPred]
  intro h
  induction' l with head tail ih
  · simp
  · apply List.chain'_cons'.mpr
    constructor
    · intro v hv
      rcases List.head?_eq_some_iff.mp (Option.mem_def.mp hv) with ⟨ys, hys⟩
      subst hys
      unfold alternatesColor.aux at h
      tauto
    · apply ih
      · simp only [List.nodup_cons] at hl
        exact hl.right
      · unfold alternatesColor.aux at h
        split at h <;> simp_all
        · rename_i v₁ v₂ vs hv
          rcases hv with ⟨hv1, hv2⟩
          subst hv2
          tauto

include hl hab in
theorem colorPred_eq_alternatesColor :
  colorPred C l a b ↔ alternatesColor C l a b := by
  constructor
  apply alternatesColor_of_colorPred; repeat assumption
  apply colorPred_of_alternatesColor; repeat assumption

theorem has_colored_nbor_of_interior {i : Nat}
  (h1 : 0 < i) (h2 : i < l.length - 1) (h3 : alternatesColor C l a b) :
  color C (l[i-1], l[i]) = a ∧ color C (l[i], l[i+1]) = b ∨
  color C (l[i-1], l[i]) = b ∧ color C (l[i], l[i+1]) = a := by
  induction' l with x xs ih generalizing i
  · simp at h2
  · have aux1 : i ≠ 0 := Nat.ne_zero_of_lt h1
    have aux2 : xs.length > 1 := by
      simp at h2
      linarith
    have aux3 : ∃ v₁ v₂ vs, (x :: xs) = v₁ :: v₂ :: vs := by
      have : xs ≠ [] := by
        apply List.ne_nil_of_length_pos
        linarith
      use x, xs.head this, xs.tail
      simp
    rcases aux3 with ⟨v₁, v₂, vs, aux3⟩
    have aux4 : xs = v₂ :: vs := by exact List.tail_eq_of_cons_eq aux3
    simp [List.getElem_cons, aux1]
    simp_rw [aux4] at ⊢ ih
    simp_rw [aux3, alternatesColor, alternatesColor.aux] at h3
    by_cases hi : i = 1
    · subst hi
      simp_all
      apply List.exists_cons_of_length_pos at aux2
      rcases aux2 with ⟨v₃, vs', hvs⟩
      subst hvs
      unfold alternatesColor.aux at h3
      simp; tauto
    · have aux5 : i > 1 := by
        exact Nat.lt_of_le_of_ne h1 fun a ↦ hi (Eq.symm a)
      have aux6 : i - 1 ≠ 0 := by
        exact Nat.sub_ne_zero_iff_lt.mpr aux5
      simp [aux6]
      specialize @ih (i - 1)
      have : i - 1 + 1 = i := by exact Nat.sub_add_cancel h1
      simp_rw [this] at ih
      apply ih
      · linarith
      · rw [aux3] at h2
        simp at ⊢ h2
        exact Nat.sub_lt_right_of_lt_add h1 h2
      · unfold alternatesColor
        tauto

-- theorem has_colored_nbor_of_middle (h : l ≠ []) (u : Vertex n) (h1 : u ∈ l)
--   (h2 : u ≠ l.head h) (h3 : u ≠ l.getLast h) :
--   color C (l.prev u h1, u) = a ∨ color C (l.next u h1, u) = a := by
--   rcases middle_of_ne_head_getLast h h1 h2 h3 with ⟨xs, ys, hxs, hys, hl⟩
--   revert h2 h3
--   simp_rw [← hl]
--   induction' xs with x xs' ih generalizing l
--   · simp_all
--   · simp
--     have : ∃ z zs, xs' ++ u :: ys = z :: zs := by
--       have : xs' ++ u :: ys ≠ [] := by simp
--       exact List.exists_cons_of_ne_nil this
--     rcases this with ⟨z, zs, heq⟩
--     simp_rw [heq] at ⊢ ih
--     rw [List.next_ne_head_ne_getLast, prev_cons_cons_of_ne_ne]

--     cases xs'
--     · simp_all
--       simp at heq
--       simp_rw [← heq]













--     sorry


structure Path (x : Vertex n) (a b : Color c) where
  val : List (Vertex n)
  containsAx : x ∈ val
  nodupAx : val.Nodup
  colorAx : alternatesColor C val a b
  aAx : a.isSome
  bAx : b.isSome
  freeAx : a ∈ freeColorsOn C x
end

variable {n c : Nat} {G : Graph n} {C : EdgeColoring c G}

def singletonPath (a b : Color c) (x : Vertex n)
  (ha : a.isSome) (hb : b.isSome) (hx : a ∈ freeColorsOn C x) :
  Path C x a b where
  val := [x]
  containsAx := by exact List.mem_singleton.mpr rfl
  nodupAx := by exact List.nodup_singleton x
  colorAx := by simp [alternatesColor]
  aAx := ha
  bAx := hb
  freeAx := hx

variable
  {a b : Color c}
  {x : Vertex n}
  {h : a.isSome ∧ b.isSome}

def dropHead (P : Path C x a b) (h1 : ∃ z zs, P.val = z :: zs ∧ x ≠ z) : Path C x a b where
  val := P.val.tail
  containsAx := by
    rcases h1 with ⟨z, zs, h1, h2⟩
    rw [h1]
    simp only [List.tail_cons]
    have := P.containsAx
    apply List.mem_of_ne_of_mem h2
    rwa [h1] at this
  nodupAx := by
    exact tail_nodup_of_nodup P.nodupAx
  colorAx := by
    have := P.colorAx
    rw [← colorPred_eq_alternatesColor] at ⊢ this
    apply List.Chain'.suffix this
    · exact List.tail_suffix P.val
    · exact tail_nodup_of_nodup P.nodupAx
    any_goals exact And.intro P.aAx P.bAx
    · exact P.nodupAx
  aAx := P.aAx
  bAx := P.bAx
  freeAx := P.freeAx

theorem path_ne_nil (P : Path C x a b) :
  P.val ≠ [] := List.ne_nil_of_mem P.containsAx

def first (P : Path C x a b) : Vertex n :=
  P.val.head (path_ne_nil P)

def last (P : Path C x a b) : Vertex n :=
  P.val.getLast (path_ne_nil P)

def isMiddle (P : Path C x a b) (u : Vertex n) :=
  u ∈ P.val ∧ u ≠ first P ∧ u ≠ last P

theorem middle_spec (P : Path C x a b) (u : Vertex n) :
  isMiddle P u → ∃ l₁ l₂ : List (Vertex n),
    l₁ ≠ [] ∧ l₂ ≠ [] ∧ l₁ ++ (u :: l₂) = P.val := by
  intro h
  simp [isMiddle, first, last] at h
  rcases h with ⟨h1, h2, h3⟩
  rw [List.head_eq_getElem] at h2
  rw [List.getLast_eq_getElem] at h3
  apply List.getElem_of_mem at h1
  rcases h1 with ⟨i, h, hi⟩
  use List.take i P.val, List.drop (i + 1) P.val
  simp_all
  repeat any_goals apply And.intro
  · contrapose! h2
    simp_rw [h2] at hi
    exact Eq.symm hi
  · exact path_ne_nil P
  · rw [← hi] at h3
    contrapose! h3
    rw [(List.Nodup.getElem_inj_iff P.nodupAx).mpr]
    apply Nat.eq_sub_of_add_eq'
    rw [add_comm]
    apply lt_or_eq_of_le at h3
    rcases h3 with hlt | heq
    · linarith
    · exact Eq.symm heq
  · simp_rw [← hi]
    simp only [List.getElem_cons_drop, List.take_append_drop]


-- theorem middle_edges (P : Path C x a b) (u : Vertex n) (h : isMiddle P u) :
--   color C (List.prev P.val u h.left, u) = a ∨
--   color C (List.next P.val u h.left, u) = a := by
--   rcases middle_spec P u h with ⟨l₁, l₂, hl₁, hl₂, hp⟩
--   -- simp_rw [← hp]
--   have aux1 : ∃ xs v₁, l₁ = xs ++ [v₁] := by
--     use l₁.take (l₁.length - 1), l₁.getLast hl₁
--     exact Eq.symm (List.take_append_getLast l₁ hl₁)
--   rcases aux1 with ⟨xs, v₁, h1⟩
--   have aux2 : ∃ v₂ ys, l₂ = v₂ :: ys := by
--     use l₂.head hl₂, l₂.tail
--     exact Eq.symm (List.head_cons_tail l₂ hl₂)
--   rcases aux2 with ⟨v₂, ys, h2⟩
--   subst h1 h2
--   simp at hp
--   simp_rw [← hp]
--   induction' xs with head tail ih generalizing P
--   · simp at ⊢ hp
--     rw [List.prev_cons_cons_of_ne, List.next_ne_head_ne_getLast,
--       List.next_cons_cons_eq]
--     · have := P.colorAx
--       unfold alternatesColor alternatesColor.aux at this
--       unfold alternatesColor.aux at this
--       rw [← hp] at this
--       simp [color_symm] at this ⊢
--       tauto
--     · simp
--     any_goals
--       by_contra hc
--       subst hc
--       have := P.nodupAx
--       rw [← hp, List.nodup_cons] at this
--       rcases this with ⟨h, _⟩
--       exact h List.mem_cons_self
--     · simp_rw [hp]
--       simp [isMiddle, last] at h
--       exact h.right.right
--   · have : ∃ z zs, tail ++ v₁ :: u :: v₂ :: ys = z :: zs := by
--       have : tail ++ v₁ :: u :: v₂ :: ys ≠ [] := by simp
--       use (tail ++ v₁ :: u :: v₂ :: ys).head this,
--         (tail ++ v₁ :: u :: v₂ :: ys).tail
--       simp
--     rcases this with ⟨z, zs, h⟩
--     simp [h] at ⊢ ih
--     rw [List.next_ne_head_ne_getLast, prev_cons_cons_of_ne_ne]
--     specialize ih (dropHead P (by use z, zs  ))







    -- simp
    -- rw [List.next_ne_head_ne_getLast]
    -- have : ∃ z zs, tail ++ [v₁] ++ u :: v₂ :: ys = z :: zs := by
    --   have : tail ++ [v₁] ++ u :: v₂ :: ys ≠ [] := by simp
    --   use (tail ++ [v₁] ++ u :: v₂ :: ys).head this,
    --     (tail ++ [v₁] ++ u :: v₂ :: ys).tail
    --   simp
    -- rcases this with ⟨z, zs, h⟩



















  -- sorry

theorem path_endpoint (P : Path C x a b) :
  x = first P ∨ x = last P := by
  by_contra h
  push_neg at h
  rcases middle_spec P x ⟨P.containsAx, h⟩ with ⟨l₁, l₂, hl₁, hl₂, hp⟩
  let v₁ := l₁.getLast hl₁
  let v₂ := l₂.head hl₂
  have h1 : color C (x, v₁) = a ∨ color C (x, v₂) = a := by
    sorry
  have h2 := P.freeAx
  simp [freeColorsOn, incidentColorsOn] at h2
  rcases h2 with ⟨_, h2⟩
  simp [color] at h1
  rcases h1 with h1 | h1
  all_goals
    apply Array.mem_of_getElem at h1
    have := P.aAx
    simp_all

-- theorem path_ne_nil (P : Path C x a b) :
--   P.val ≠ [] := List.ne_nil_of_mem P.containsAx


-- theorem path_colorPred (P : Path C x a b h) :
--   colorPred C P.val a b := by
--   apply (colorPred_eq_alternatesColor C P.val P.nodupAx a b h).mpr
--   exact P.colorAx


-- def lastColor (P : Path C x a b h) : Color c :=
--   match P.val with
--   | v₁ :: v₂ :: _ => color C (v₁, v₂)
--   | _ => none

-- def nextColor (P : Path C x a b h) : Color c :=
--   if lastColor P = a then b else a

-- def findNextVertex (P : Path C x a b h) : Option (Vertex n) :=
--   findNborWithColor C (P.val.head (path_ne_nil P)) (nextColor P)

-- theorem nextColor_not_mem (P : Path C x a b h) (h1 : (findNextVertex P).isSome) :
--   (findNextVertex P).get h1 ∉ P.val := by
--   apply Option.isSome_iff_exists.mp at h1
--   rcases h1 with ⟨u, hu⟩
--   simp_rw [hu, Option.get_some]
--   simp [findNextVertex, findNborWithColor] at hu
--   by_contra hc


--   sorry

-- theorem lastColor_nonempty_spec (P : Path C x a b h) :
--   P.val.length > 1 → lastColor P = a ∨ lastColor P = b := by sorry


-- theorem lastColor_empty_spec (P : Path C x a b h) :
--   P.val.length ≤ 1 → lastColor P = none := by sorry



-- def prev (P : Path C x a b h) (v : Vertex n) : Option (Vertex n) :=
--   let i := P.val.idxOf v
--   have := List.length_pos_iff.mpr (List.ne_nil_of_mem P.containsAx)
--   if h : i = 0 then none else
--     some (P.val[i - 1]'(by
--     simp [i]; grw [List.idxOf_le_length]; exact Nat.sub_one_lt_of_lt this))

-- def next (P  : Path C x a b h) (v : Vertex n) : Option (Vertex n) :=
--   let i := P.val.idxOf v
--   have := List.length_pos_iff.mpr (List.ne_nil_of_mem P.containsAx)
--   if h : i < (P.val.length - 1) then some P.val[i + 1] else none


-- def nbors_only (P : Path C x a b h) (v : Vertex n) (h : v ∈ P.val) :
--   ∀ u ∈ (nbhd G v).val, some u = prev P v ∨ some u = next P v := by


--   sorry


/- The first elem in the fan does not have a b-colored neighbor -/




-- theorem middle_nbhd_size (P : Path C x a b h) :
--   ∀ u ∈ P.val, isMiddle P.val u →
--     ∃ v₁ v₂, (P.val.filter (· ∈ (nbhd G u).val)).toFinset = [v₁, v₂].toFinset := by
--   intro u h1 ⟨p₁, p₂, hp1, hp2, hp⟩
--   use p₁.getLast hp1, p₂.head hp2

--   have := P.nodupAx
--   rw [hp] at this
--   apply List.nodup_middle.mp at this
--   simp at this
--   rcases this with ⟨⟨hu1, hu2⟩, this⟩
--   rcases List.nodup_append.mp this with ⟨hp1, hp2, _⟩



--   have := path_colorPred P
--   simp_rw [colorPred, hp] at this
--   apply List.chain'_split.mp at this


--   -- List.chain'_split

--   sorry

end Path
