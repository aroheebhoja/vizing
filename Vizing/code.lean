import Std
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Nat.SuccPred

def foo : Array (Array Nat) :=
  #[#[0]]

/-
Need data representations for:
- Graph -- Incidence list - Array (Array Nat)
- Color set -- Nat (for the size of the coloring) (≤ Δ(G))
- Edge set -- List Vertex × Vertex
- (Partial) coloring -- Incidence matrix (0 if uncolored, 1...k+1 else) - Array (Array Nat)
- Fan -- List Nat
- cd-path (subset of edge set) -- List Edge

Need functions for:
- DONE Find max degree of a graph
- DONE Find maximal fan on a vertex
- DONE Find free colors on a vertex
- DONE Find a maximal cd-path through a vertex
- DONE Find a subfan of a fan
- DONE Set the color of an edge
- DONE Rotate a fan
-/

/-

TODO:
  1. Use fintypes to represent vertices and colors and modify array accesses
  2. Fill in termination proof for fan construction
  3. Figure out termination proof for cdpath construction
  4. Start proving correctness of functions
-/

#check Array.erase
#check Array.contains

-- Use fintypes

abbrev Vertex := Nat
abbrev Color := Nat
abbrev Graph := Array (Array (Vertex))
abbrev Edge := (Vertex) × (Vertex)
abbrev EdgeColoring := Array (Array (Color))
abbrev Fan := List (Vertex)
abbrev Path := List (Edge)

def maxDegree (G : Graph) :=
  let degrees := (G.map (fun nbors => nbors.size))
  match degrees.getMax? (· < ·) with
  | some d => d
  | none => 0

def edgeSet (G : Graph) : List (Edge) :=
  (G.mapIdx (fun u nbors => (nbors.map (fun v => (u, v))).toList)).toList.flatten

def getUncoloredNbors (G : Graph) (x : Vertex) (C : EdgeColoring) : Array Vertex :=
  G[x]!.filter (fun n => (C[x]![n]! = 0))

def isUncolored (C : EdgeColoring) (u : Vertex) (v : Vertex) : Bool :=
  C[u]![v]! == 0

def color (C : EdgeColoring) (u : Vertex) (v : Vertex) : Color :=
  C[u]![v]!

def getIncidentColors (G : Graph) (x : Vertex) (C : EdgeColoring) : Array Color :=
  G[x]!.filterMap (fun n => if C[x]![n]! != 0 then some C[x]![n]! else none)

def getNeighbor (G : Graph) (x : Vertex) (C : EdgeColoring) (c : Color) :=
  match G[x]!.toList.filter (fun n => C[x]![n]! == c) with
  | [] => none
  | n :: _ => some n

def getFreeColors (G : Graph) (x : Vertex) (C : EdgeColoring) (Δ : Nat) : Array Color :=
  let incidentColors := getIncidentColors G x C
  (Array.range (Δ+2)).filter (fun c => not (incidentColors.contains c) && (c != 0))

def setEdgeColor (u : Vertex) (v : Vertex) (C : EdgeColoring) (c : Color) :=
  let C := C.set! u <| C[u]!.set! v c
  C.set! v <| C[v]!.set! u c

def fan (G : Graph) (x : Vertex) (y : Vertex) (C : EdgeColoring) (Δ : Nat) :=
  let nbors := G[x]!.toList.erase y
  (fan' [y] nbors).reverse
where fan' : Fan → List Vertex → Fan
  -- Case 1: No more neighbors to extend the fan with
  | [], _ => []
  -- Case 2: We have a partial fan
  | f :: fs, c =>
    let freeColors := getFreeColors G f C Δ
    -- Q: Is there a way to write this case so I don't have to write a termination proof?
    let c' := c.filter (fun y => freeColors.contains (color C x y))
    match h' : c' with
    | [] => f :: fs
    | n :: ns => have : (c.erase n).length < c.length := by
                  have h1 : n ∈ c' := by
                    rw [h']
                    apply List.mem_cons_self n ns
                  have h2 : n ∈ c := by
                    simp only [List.mem_filter, c'] at h1
                    exact h1.left
                  have h3 : c.length > 0 := by
                    apply List.length_pos_iff_exists_mem.mpr
                    use n
                  rw [List.length_erase_of_mem]
                  · exact Nat.sub_one_lt_of_lt h3
                  · exact h2
                fan' (n :: (f :: fs)) (c.erase n)
termination_by _ c => c.length

-- (h: whatever condition guarantees termination)
partial def cdPath (G : Graph) (x : Vertex) (C : EdgeColoring) (c d : Color) :=
  let p1 := extendPath x c []
  let p2 := extendPath x d []
  p1 ++ (p2.reverse)
where extendPath (u : Vertex) (a : Color) (p : Path) : Path :=
  let us := G[u]!.filter (fun n => color C u n == a)
  let b := if a == c then d else c
  match us.toList with
  | [] => p
  | u'::_ => extendPath u' b ((u', u)::p)

def subfan (G : Graph) (C : EdgeColoring) (Δ : Nat) (F : Fan) (c : Color) :=
  match F with
  | [] => []
  | f :: fs =>
    let freeColors := getFreeColors G f C Δ
    if freeColors.contains c then [f] else f :: (subfan G C Δ fs c)

def rotateFan (x : Vertex) (F : Fan) (c : Color) (A : EdgeColoring) : EdgeColoring :=
  rotate (F.reverse) c A where
  rotate : Fan → Color → EdgeColoring → EdgeColoring
  | [], _, C => C
  | f :: fs, a, C =>
    -- Find the previous color of the edge
    let a' := color C x f
    -- Color the edge with the new color
    let C' := setEdgeColor x f C a
    rotate fs a' C'

def invertPath (C : EdgeColoring) (P : Path) (c d : Color) :=
  match P with
  | [] => C
  | (u, v)::P' =>
    let a := if color C u v == c then d else c
    invertPath (setEdgeColor u v C a) P' c d

def edgeColor (G : Graph) : EdgeColoring :=
  let A : EdgeColoring := mkArray G.size (mkArray G.size 0)
  let Δ := maxDegree G
  let E := edgeSet G
  extend A Δ E where
  extend : EdgeColoring → Nat → List Edge → EdgeColoring
  | C, _, [] => C
  | C, Δ, (x, y)::E' =>
    let F := fan G x y C Δ
    let c := (getFreeColors G x C Δ)[0]!
    let d := (getFreeColors G y C Δ)[0]!
    -- dbg_trace s!"free colors chosen: {c} {d}"
    let P := cdPath G x C c d
    let C' := invertPath C P c d
    let F' := subfan G C' Δ F d
    let C'' := rotateFan x F' d C'
    extend C'' Δ E'


#check edgeColor #[#[1,2], #[0,2], #[0,1]]
