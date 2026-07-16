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
  {X : Type*}
  [ConvexSpace ℝ X]
  [AddCommGroup X]
  [Module ℝ X]
  [IsModuleConvexSpace ℝ X]

structure isGraphPolytopeGenerated
    (P : Polytope ℝ X) (V : Finset X) (G : SimpleGraph V) : Prop where
  h_carrier : _root_.convexHull ℝ V = P.carrier
  h_extreme : ∀ v ∈ V, Convexity.IsExtreme ℝ P.carrier {v}
  h_2 : ∀ (i j : X),  (hi : i ∈ V) → (hj : j ∈ V) →
    G.Adj ⟨i,hi⟩ ⟨j,hj⟩ ↔
    Convexity.IsExtreme ℝ P.carrier [i -[ℝ] j]



--this lemma should not be proved since in current mathlib this should not be a problem?
lemma patch (R : Type u_1) {X : Type u_2} [Semiring R] [PartialOrder R]
  [IsStrictOrderedRing R] [AddCommMonoid X] [Module R X]
  [ConvexSpace R X] (S : Set X) :
  Convexity.convexHull R S = _root_.convexHull R S := sorry

omit [IsModuleConvexSpace ℝ X] in
lemma VertexInPolytope {P : Polytope ℝ X} {V : Finset X} {G : SimpleGraph V}
  (h : isGraphPolytopeGenerated P V G) (v : X) (vmem : v ∈ V) :
  v ∈ P.carrier := by
  have g : _root_.convexHull ℝ V = P.carrier := h.h_carrier
  rw [← g]
  apply Set.mem_of_subset_of_mem _ vmem
  rw[← patch]
  apply Convexity.subset_convexHull_self

def ConeAtVertex (R : Type*) [Semiring R] [PartialOrder R]
    (X : Type*) [AddCommGroup X] [Module R X]
    {V : Finset X} (G : SimpleGraph V) (v : X) (vmem : v ∈ V) : Set X :=
  { x | ∃ c : V → R,
      (∀ x, 0 ≤ c x) ∧
      (∀ x, c x ≠ 0 → G.Adj ⟨v, vmem⟩ x) ∧
      x = v + ∑ x : V, c x • ((x : X) - v) }

lemma PolytopeContainedInCone {P : Polytope ℝ X} {V : Finset X} {G : SimpleGraph V}
    (h : isGraphPolytopeGenerated P V G) (v : X) (vmem : v ∈ V) :
    P.carrier ⊆ ConeAtVertex ℝ X G v vmem := by sorry


variable [TopologicalSpace X]

lemma IncreasingPathLemma {P : Polytope ℝ X} {V : Finset X} {G : SimpleGraph V}
    (h : isGraphPolytopeGenerated P V G)
    (f : StrongDual ℝ X) {v : X} (vmem : v ∈ V) (Vne : V.Nonempty)
    (hv : f v < Finset.max' (Finset.image f V) (Finset.image_nonempty.mpr Vne))
    :
    (∃ (w : X) (wmem : w ∈ V), G.Adj ⟨v, vmem⟩ ⟨w, wmem⟩ ∧ f v < f w) := by
    have aux₀ : ∃ p ∈ V, f p = Finset.max' (Finset.image f V) (Finset.image_nonempty.mpr Vne) :=
      Finset.mem_image.mp <| Finset.max'_mem _ <| Finset.image_nonempty.mpr Vne
    obtain ⟨p, pmem, hfp⟩ := aux₀
    have aux' : f v < f p := by
      exact hfp ▸ hv
    have hp: p ∈ ConeAtVertex ℝ X G v vmem := by
      apply PolytopeContainedInCone h v vmem
      exact VertexInPolytope h p pmem
    obtain ⟨x, hx1, hx2, hx3⟩ := hp
    rw [hx3, map_add, map_sum] at aux'
    simp only [map_smul, map_sub, smul_eq_mul] at aux'
    have hsum : (0 : ℝ) < ∑ u : V, x u * (f u - f v) := by grind
    obtain ⟨t, -, ht⟩ : ∃ t ∈ Finset.univ, (0 : ℝ) < x t * (f ↑t - f v) := by
      by_contra hcon
      push Not at hcon
      exact absurd (Finset.sum_nonpos fun t _ => hcon t (Finset.mem_univ t)) (not_le.mpr hsum)
    rcases mul_pos_iff.mp ht with ⟨hc, hf⟩ | ⟨hc, -⟩
    · exact ⟨(t : X), t.2, hx2 t hc.ne', by grind⟩
    exact absurd (hx1 t) (not_le.mpr hc)

omit [ConvexSpace ℝ X] [TopologicalSpace X] in
open scoped Pointwise in
lemma convex_vsub_comm (S : Set X) :
    (_root_.convexHull ℝ (S -ᵥ S)) = (_root_.convexHull ℝ S) -ᵥ (_root_.convexHull ℝ S) := by
  have hvsub : ∀ A B : Set X, A -ᵥ B = A - B := by
    intro A B; ext x; simp [Set.mem_vsub, Set.mem_sub, vsub_eq_sub]
  rw [hvsub, hvsub, convexHull_sub]

omit [TopologicalSpace X] in
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
    have : S -ᵥ S ⊆ (_root_.convexHull ℝ) S -ᵥ (_root_.convexHull ℝ) S
    := Set.vsub_subset_vsub (subset_convexHull ℝ S ) (subset_convexHull ℝ S )
    grind

omit [TopologicalSpace X] in
theorem balinski_1 {P : Polytope ℝ X} {V : Finset X} {G : SimpleGraph V} (hV : Finset.Nonempty V)
(hG : isGraphPolytopeGenerated P V G) : dimPolytope P.carrier < Nat.card ↥V := by
  classical
  unfold dimPolytope
  set n := Nat.card V
  rw[← hG.h_carrier, vectorSpan_of_convexHull]
  have : ↑V = Finset.image id V := by simp
  rw[this]
  have hn0 :  1 ≤ n := by simp only [Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.one_le_card, n] ; exact hV
  have
  := finrank_vectorSpan_image_finset_le ℝ id V (n := n - 1) (by unfold n at *; simp at this ⊢;grind)
  grind

theorem balinski {P : Polytope ℝ X} {V : Finset X} {G : SimpleGraph V} (hV : Finset.Nonempty V)
(hG : isGraphPolytopeGenerated P V G) :
  IsVertexConnected G (dimPolytope (V := X) (P.carrier))
    := by
        classical
        unfold IsVertexConnected
        constructor
        · exact balinski_1 hV hG
        · intros S H
          have v₁ : @Set.Elem (↥V) (↑S)ᶜ := sorry --Cardinality argument (apply H + balinski_1)
          obtain ⟨v₁, hv⟩ := v₁
          have hf : ∃ f : StrongDual ℝ X, ∃ c : ℝ, (f v₁ = c ∧ (∀ s ∈ S, f s = c)):= sorry
          obtain ⟨f, c, hf⟩ := hf
          set S₁ := {v : V | v ∉ S ∧ c ≤ f v}
          set S₂ := {v : V | v ∉ S ∧ f v ≤ c}
          have h1 : (G.induce S₁).Connected := by
            /-Show that f is maximized on a face, the graph of face is connected as it is a
            polytope, every other vertex has path to face by IncreasingLemma, apply
            Subgraph_Connected_Reachable_Implies_Connected -/
            sorry
          have h2 : (G.induce S₂).Connected := by
            /-Apply proof of h1 to -f -/
            sorry
          have hv1 : v₁ ∈ S₁ ∩ S₂ := by
            grind
          apply Union_of_two_connected_subgraphs (induce (↑S)ᶜ G)
            {v | c ≤ f v} {v | f v ≤ c}
          · intro v
            grind
          · use ⟨v₁,hv⟩
            constructor
            · simp only [Set.mem_setOf_eq]
              rw[hf.1]
            simp only [Set.mem_setOf_eq]
            rw[hf.1]
          · sorry --is exactly h1 but type mismatch
          · sorry --is exactly h2 but type mismatch
end
