import Polyhedral.Icarm.kconnectivity
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Lattice
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Segment
import Polyhedral.Polyhedral.Basic
import Polyhedral.Polyhedral.Faces
import Polyhedral.Mathlib.Geometry.Convex.ConvexSpace.Polytope.Face

open Convexity Convex SimpleGraph

variable (R : Type*)
variable {V A : Type*}

open Convexity ConvexSet Affine

variable [LinearOrder R] [Ring R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V A]
attribute [local instance] AddTorsor.toConvexSpace

noncomputable def dimPolytope (C : Set A) : ℕ :=
  Module.finrank R (affineSpan R C).direction

section

variable
  (R : Type*)
  (X : Type*)
  [Ring R]
  [PartialOrder R]
  [IsStrictOrderedRing R]
  [ConvexSpace R X]
  [AddCommGroup X]
  [Module R X]

structure isGraphPolytopeGenerated
    (P : Polytope R X) (V : Finset X) (G : SimpleGraph V) : Prop where
  h_carrier : Convexity.convexHull R V = P.carrier
  h_2 : ∀ (i j : X),  (hi : i ∈ V) → (hj : j ∈ V) →
    G.Adj ⟨i,hi⟩ ⟨j,hj⟩ ↔
    Convexity.IsExtreme R P.carrier [i -[R] j]

theorem balinski {P : Polytope R X} {V : Finset X} {G : SimpleGraph V}
(hG : isGraphPolytopeGenerated R X P V G) :
  IsVertexConnected G (dimPolytope R (V := X) (P.carrier))
    := sorry --the graph G with isGraphPolytopeGenerated P V G is d-connected for every d-polytope P
