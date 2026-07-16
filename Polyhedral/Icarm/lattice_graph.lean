import Polyhedral.Icarm.kconnectivity
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Lattice
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.Hull
import Mathlib.Geometry.Convex.Set
import Polyhedral.Polyhedral.Basic
import Polyhedral.Polyhedral.Faces
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Face
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

open Convexity Convex SimpleGraph

variable {V A : Type*}

open Convexity ConvexSet Affine

variable [AddCommGroup V] [Module ℝ V] [AddTorsor V A]

noncomputable def dimPolytope (C : Set A) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ C) --(affineSpan ℝ C).direction
section

variable
  (X : Type*)
  [ConvexSpace ℝ X]
  [AddCommGroup X]
  [Module ℝ X]
  [IsModuleConvexSpace ℝ X]

structure isGraphPolytopeGenerated
    (P : Polytope ℝ X) (V : Finset X) (G : SimpleGraph V) : Prop where
  h_carrier : _root_.convexHull ℝ V = P.carrier
  h_2 : ∀ (i j : X),  (hi : i ∈ V) → (hj : j ∈ V) →
    G.Adj ⟨i,hi⟩ ⟨j,hj⟩ ↔
    Convexity.IsExtreme ℝ P.carrier [i -[ℝ] j]

lemma patch (R : Type u_1) {X : Type u_2} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [AddCommMonoid X]
  [Module R X]
  [ConvexSpace R X] (S : Set X) : Convexity.convexHull R S = _root_.convexHull R S := sorry

lemma convex_vsub_comm (S : Set X) [IsModuleConvexSpace ℝ X] :
(_root_.convexHull ℝ (S -ᵥ S)) = (_root_.convexHull ℝ S)-ᵥ (_root_.convexHull ℝ S) := by
  ext x ; constructor <;> intros h
  · rw [Set.mem_vsub] at ⊢
    rw[mem_convexHull_iff_exists_fintype] at h
    sorry
  · rw[Set.mem_vsub] at h
    rw [@mem_convexHull_iff_exists_fintype]
    sorry

lemma vectorSpan_of_convexHull (S : Set X) :
 vectorSpan ℝ  (_root_.convexHull ℝ S) = (vectorSpan ℝ S) := by
  ext x ; unfold vectorSpan
  simp only [Submodule.mem_span]
  constructor <;> intro h1 p h2
  · rw[← convex_vsub_comm] at h1
    specialize h1 p
    apply h1
    have : IsConvexSet ℝ (X := X) p :=by apply p.isConvexSet
    have tt := (IsConvexSet.convexHull_subset_iff (this) (s := S -ᵥ S)).2 h2
    rw[patch] at tt
    exact tt
  · specialize h1 p
    apply h1
    have : S -ᵥ S ⊆ (_root_.convexHull ℝ) S -ᵥ (_root_.convexHull ℝ) S := Set.vsub_subset_vsub (subset_convexHull ℝ S ) (subset_convexHull ℝ S )
    grind

theorem balinski {P : Polytope ℝ X} {V : Finset X} {G : SimpleGraph V} (hV : Finset.Nonempty V)
(hG : isGraphPolytopeGenerated X P V G) :
  IsVertexConnected G (dimPolytope (V := X) (P.carrier))
    := by
        classical
        unfold IsVertexConnected
        constructor
        · unfold dimPolytope
          set n := Nat.card V
          rw[← hG.h_carrier, vectorSpan_of_convexHull]
          have : ↑V = Finset.image id V := by simp
          rw[this]
          have hn0 :  1 ≤ n := by simp[n] ; exact hV
          have := finrank_vectorSpan_image_finset_le ℝ id V (n := n - 1) (by unfold n at *; simp at this ⊢;grind)
          grind
        · intros S H
          simp only [connected_iff_exists_forall_reachable]
          have v₁ : @Set.Elem (↥V) (↑S)ᶜ := sorry
          apply Exists.intro v₁
          · intro w
            unfold Reachable
            constructor
            constructor
            · sorry
            · sorry
            · sorry
