import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open SimpleGraph Finset

namespace SimpleGraph

variable {V E : Type*} [LinearOrder E]

def isArgmax (f : V → E) (v : V) : Prop := ∀ u, f u ≤ f v

def climbing (f : V → E) (G : SimpleGraph V) : Prop :=
  ∀ u, ¬isArgmax f u → ∃ v, G.Adj u v ∧ f u < f v

structure ClimbingSimpleGraph (f : V → E) extends SimpleGraph V where
  choice : V → Option V
  spec (u : V) : match choice u with
    | none => isArgmax f u
    | some v => toSimpleGraph.Adj u v ∧ f u < f v

noncomputable def ClimbingSimpleGraphOfClimbing
    {f : V → E} {G : SimpleGraph V} (hG : climbing f G) :
    ClimbingSimpleGraph f where
  toSimpleGraph := G
  choice v := by
    by_cases hv : isArgmax f v
    · exact none
    · exact some <| Classical.choose <| hG v hv
  spec u := by grind

theorem isArgmax_of_none {f : V → E} {G : ClimbingSimpleGraph f}
    {u : V} (hu : G.choice u = none) : isArgmax f u := by
  grind [G.spec u]

theorem le_of_choice_some {f : V → E} {G : ClimbingSimpleGraph f}
    {u v : V} (huv : G.choice u = some v) : f u < f v := by
  grind [G.spec u]

theorem termination_condition [Fintype V] {f : V → E} {u v : V} (hab : f u < f v) :
    #{w | f v < f w} < #{w | f u < f w} := by
  apply card_lt_card
  constructor
  · grind
  · rw [not_subset]; use v; aesop

def listOfClimbing [Fintype V] {f : V → E} (G : ClimbingSimpleGraph f) (u : V) :
    List V :=
  match _ : G.choice u with
  | none => [u]
  | some v => u :: listOfClimbing G v
  termination_by #{v | f u < f v}
  decreasing_by exact termination_condition <| le_of_choice_some (by assumption)

theorem listOfClimbing_none
    [Fintype V] {f : V → E} {G : ClimbingSimpleGraph f} {u : V}
    (h : G.choice u = none) : listOfClimbing G u = [u] := by
  unfold listOfClimbing
  rw [h]

theorem listOfClimbing_some
    [Fintype V] {f : V → E} {G : ClimbingSimpleGraph f} {u v : V}
    (h : G.choice u = some v) : listOfClimbing G u = u :: listOfClimbing G v := by
  nth_rewrite 1 [listOfClimbing]
  rw [h]

theorem nonempty_listOfClimbing
    [Fintype V] {f : V → E} (G : ClimbingSimpleGraph f) (u : V) :
    listOfClimbing G u ≠ [] := by
  unfold listOfClimbing
  aesop

def isWalk (G : SimpleGraph V) (L : List V) : Prop :=
  match L with
  | [] => True
  | [_] => True
  | u :: v :: L' => G.Adj u v ∧ isWalk G (v :: L')

theorem isWalk_pair {G : SimpleGraph V} {a b : V} (adj : G.Adj a b) :
    isWalk G [a, b] :=
  ⟨adj, by trivial⟩

theorem cons_listOfClimbing
    [Fintype V] {f : V → E} {G : ClimbingSimpleGraph f}
    {u v : V} (huv : G.choice u = some v) :
    u :: listOfClimbing G v = listOfClimbing G u := by
  nth_rewrite 2 [listOfClimbing]
  rw [huv]

def list_toWalk
    {G : SimpleGraph V} {L : List V}
    (walkL : isWalk G L) (notnilL : L ≠ []) :
    Walk G (List.head L notnilL) (List.getLast L notnilL) :=
  match L with
  | [] => False.elim <| notnilL rfl
  | [v] => by rfl
  | u :: v :: L' => Walk.cons walkL.1 <| list_toWalk walkL.2 _

theorem isWalk_listOfClimbing
    [Fintype V] {f : V → E} (G : ClimbingSimpleGraph f) (u : V) :
    isWalk G.toSimpleGraph (listOfClimbing G u) := by
  unfold listOfClimbing
  split
  · trivial
  · rename_i v _
    unfold listOfClimbing
    have uRv : G.Adj u v ∧ f u < f v := by grind [G.spec u]
    split
    · exact isWalk_pair uRv.1
    · refine ⟨uRv.1, ?_⟩
      rw [cons_listOfClimbing (by assumption)]
      apply isWalk_listOfClimbing
  termination_by #{v | f u < f v}
  decreasing_by exact termination_condition uRv.2

def isIncreasing (f : V → E) (L : List V) : Prop :=
  match L with
  | [] => True
  | [_] => True
  | u :: v :: L' => f u < f v ∧ isIncreasing f (v :: L')

theorem isIncreasing_pair {f : V → E} {a b : V} (adj : f a < f b) :
    isIncreasing f [a, b] :=
  ⟨adj, by trivial⟩

theorem isIncreasing_listOfClimbing
    [Fintype V] {f : V → E} (G : ClimbingSimpleGraph f) (u : V) :
    isIncreasing f (listOfClimbing G u) := by
  unfold listOfClimbing
  split
  · trivial
  · rename_i v huv
    have uRv : G.Adj u v ∧ f u < f v := by grind [G.spec u]
    unfold listOfClimbing
    split
    · exact isIncreasing_pair uRv.2
    · refine ⟨uRv.2, ?_⟩
      rw [cons_listOfClimbing (by assumption)]
      apply isIncreasing_listOfClimbing
  termination_by #{v | f u < f v}
  decreasing_by exact termination_condition uRv.2

theorem getLast_listOfClimbing'
    [Fintype V] {f : V → E} (G : ClimbingSimpleGraph f) (u : V) :
    G.choice (
      List.getLast (listOfClimbing G u) (nonempty_listOfClimbing _ _)
    ) = none := by
  cases ch : G.choice u
  · simp_rw [listOfClimbing_none ch]
    rwa [List.getLast_singleton]
  · simp_rw [listOfClimbing_some ch]
    rw [List.getLast_cons (nonempty_listOfClimbing _ _)]
    apply getLast_listOfClimbing'
  termination_by #{v | f u < f v}
  decreasing_by exact termination_condition <| le_of_choice_some (by assumption)

theorem getLast_listOfClimbing
    [Fintype V] {f : V → E} (G : ClimbingSimpleGraph f) (u : V) :
    isArgmax f <| List.getLast (listOfClimbing G u) (nonempty_listOfClimbing _ _) :=
  isArgmax_of_none <| getLast_listOfClimbing' _ _

theorem listOfClimbing_head
    [Fintype V] {f : V → E} (G : ClimbingSimpleGraph f) (u : V) :
    (listOfClimbing G u).head (nonempty_listOfClimbing _ _) = u := by
  unfold listOfClimbing
  grind

theorem walkOfClimbingSimpleGraph [Finite V] {f : V → E} (G : ClimbingSimpleGraph f)
    (u : V) : ∃ v, isArgmax f v ∧ Nonempty (Walk G.toSimpleGraph u v) := by
  have := Fintype.ofFinite V
  let L := listOfClimbing G u
  have nonnilL : L ≠ [] := nonempty_listOfClimbing _ _
  let wL := list_toWalk (isWalk_listOfClimbing G u) nonnilL
  use L.getLast nonnilL
  refine ⟨getLast_listOfClimbing _ _, ?_⟩
  rw [listOfClimbing_head] at wL
  exact Nonempty.intro wL

theorem reachable_of_climbing [Finite V]
    {f : V → E} {G : SimpleGraph V} (hG : climbing f G)
    (u : V) : ∃ v, isArgmax f v ∧ G.Reachable u v := by
  let G' := ClimbingSimpleGraphOfClimbing hG
  obtain ⟨v, maxv, exists_walk⟩ := walkOfClimbingSimpleGraph G' u
  refine ⟨v, maxv, Walk.reachable <| Classical.choice exists_walk⟩

end SimpleGraph
