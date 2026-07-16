import Mathlib

open SimpleGraph

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- Two walks from u to v are internally disjoint if the only vertices they share
are the two endpoints. -/
def Walk.InternallyDisjoint {u v : V} (p q : G.Walk u v) : Prop :=
  ∀ w, w ∈ p.support → w ∈ q.support → w = u ∨ w = v

/-- Definition 1 of k-connectedness:
G is k-connected if it has more than `k` vertices, and deleting any set of fewer than `k` vertices
leaves a connected graph. -/
def IsVertexConnected (k : ℕ) : Prop :=
  k < Nat.card V ∧
    ∀ S : Finset V, S.card < k → (G.induce ((S : Set V)ᶜ)).Connected


/-- Definition 2 of k-connectedness:
  G is k-connected if ithas more than `k` vertices, and any two distinct vertices are joined by
`k` pairwise internally disjoint paths. -/
def IsVertexConnected' (k : ℕ) : Prop :=
  k < Nat.card V ∧
    ∀ u v : V, u ≠ v →
      ∃ f : Fin k → G.Path u v,
        Function.Injective f ∧
          ∀ i j, i ≠ j →
            Walk.InternallyDisjoint G (f i : G.Walk u v) (f j : G.Walk u v)



/-- Lemma: A walk that is entirely contained in a subset if vertices induces a reachable
  pair in the induced graph. -/
lemma WalkImpliesReachable {G : SimpleGraph V} {t : Set V} {u v : V} :
    ∀  (p : G.Walk u v), (∀ x ∈ p.support, x ∈ t) →
      ∀ (hu : u ∈ t) (hv : v ∈ t), (G.induce t).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
      intro p
      induction p with
      | nil => intro _ _ _ ; simp only [Reachable.rfl]
      | @cons a b c hab q ih =>
    intro hsup hu hv
    have hb : b ∈ t := hsup b (by
      rw [Walk.support_cons]; exact List.mem_cons_of_mem _ q.start_mem_support)
    have hqsup : ∀ x ∈ q.support, x ∈ t := fun x hx =>
      hsup x (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hx)
    have hadj : (G.induce t).Adj ⟨a, hu⟩ ⟨b, hb⟩ := hab
    exact hadj.reachable.trans (ih hqsup hb hv)


/-- Theorem: If G is k-connected in the sense of definition 2, it is
  k-connected in the sense of definition 1. -/
theorem IsVertexConnected'.toIsVertexConnected {G : SimpleGraph V} {k : ℕ}
    (h : G.IsVertexConnected' k) : G.IsVertexConnected k := by
  obtain ⟨hcard, hpaths⟩ := h
  haveI : Finite V := by
    have : 0 < Nat.card V := lt_of_le_of_lt (Nat.zero_le k) hcard
    exact Nat.finite_of_card_ne_zero (by grind)
  haveI : Fintype V := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card] at hcard
  rw[IsVertexConnected, Nat.card_eq_fintype_card]
  constructor
  · apply hcard
  intro s hs
  rw [SimpleGraph.connected_iff]
  constructor
  · -- Preconnected
    rintro a b
    by_cases hab : a = b
    · subst hab; exact Reachable.refl a
    · have hab' : (a : V) ≠ (b : V) := fun hh => hab (Subtype.ext hh)
      obtain ⟨f, _, hf_disj⟩ := hpaths (a : V) (b : V) hab'
      have ha_s : (a : V) ∉ s := by apply a.2
      have hb_s : (b : V) ∉ s := by apply b.2
      -- Pigeonhole: some path avoids `s`.
      have hexists : ∃ i, ∀ x ∈ (f i : G.Walk (a : V) (b : V)).support, x ∉ s := by
        by_contra hcon
        push Not at hcon
        choose x hxsup hxs using hcon
        have hxinj : Function.Injective x := by
          intro i j hij
          by_contra hne
          have hd := hf_disj i j hne
          have hxj' : x i ∈ (f j : G.Walk (a : V) (b : V)).support := by
            rw [hij]; exact hxsup j
          rcases hd (x i) (hxsup i) hxj' with hh | hh
          · exact ha_s (hh ▸ hxs i)
          · exact hb_s (hh ▸ hxs i)
        have hle : Fintype.card (Fin k) ≤ Fintype.card s :=
          Fintype.card_le_of_injective (fun i => (⟨x i, hxs i⟩ : s))
            (fun i j hij => hxinj (Subtype.ext_iff.mp hij))
        rw [Fintype.card_fin, Fintype.card_coe] at hle
        exact absurd hle (not_le.mpr hs)
      obtain ⟨i, hi⟩ := hexists
      have hsupp : ∀ x ∈ (f i : G.Walk (a : V) (b : V)).support, x ∈ ((s : Set V)ᶜ) :=
        fun x hx => by grind
      apply WalkImpliesReachable (f i : G.Walk (a : V) (b : V)) hsupp a.2 b.2
  · -- Nonempty
    obtain ⟨y, hy⟩ : ∃ y, y ∉ s := by
      by_contra hcon
      push Not at hcon
      have hcard_eq : s.card = Fintype.card V := by
        rw [Finset.eq_univ_iff_forall.mpr hcon, Finset.card_univ]
      have : s.card < Fintype.card V := lt_trans hs hcard
      grind
    exact ⟨⟨y, by grind⟩⟩


theorem Subgraph_Connected_Reachable_Implies_Connected {G : SimpleGraph V}
 {S : Set V} (h : (G.induce S).Connected)
 (h' : ∀ v ∈ (S : Set V)ᶜ, (∃ w ∈ S, G.Reachable v w)) : G.Connected := by
  rw[(G.induce S).connected_iff_exists_forall_reachable] at h
  have g : ∀ u : V, ∃ w ∈ S, G.Reachable u w := by
    intro u
    by_cases hu : u ∈ S
    · use u
    · obtain ⟨w, _, _⟩ := h' u hu
      use w
  rw [SimpleGraph.connected_iff]
  constructor
  · obtain ⟨c, hc⟩ := h
    intro u v
    obtain ⟨a, haS, hua⟩ := g u
    obtain ⟨b, hbS, hvb⟩ := g v
    have hca : G.Reachable (c : V) a := by
      have h₁ : (G.induce S).Reachable c ⟨a, haS⟩ := hc ⟨a, haS⟩
      exact h₁.map (Embedding.induce S).toHom
    have hcb : G.Reachable (c : V) b := by
      have h₂ : (G.induce S).Reachable c ⟨b, hbS⟩ := hc ⟨b, hbS⟩
      exact h₂.map (Embedding.induce S).toHom
    exact ((hua.trans hca.symm).trans hcb).trans hvb.symm
  · obtain ⟨s⟩ := h.nonempty
    use s


theorem Union_of_two_connected_subgraphs (G : SimpleGraph V) (S₁ S₂ : Set V) :
  (∀ v : V, v ∈ S₁ ∪ S₂) → ((S₁ ∩ S₂).Nonempty) → (G.induce S₁).Connected
   → (G.induce S₂).Connected → G.Connected := by
  intro hsu hsi hs1 hs2
  obtain ⟨v, hv1, hv2⟩ := hsi
  rw[connected_iff] at hs1 hs2
  have g₁ : ∀ u ∈ S₁, G.Reachable v u := by
    intro u hu
    have h : (G.induce S₁).Reachable ⟨v, hv1⟩ ⟨u, hu⟩ := hs1.1 ⟨v, hv1⟩ ⟨u, hu⟩
    exact h.map (Embedding.induce S₁).toHom
  have g₂ : ∀ u ∈ S₂, G.Reachable v u := by
    intro u hu
    have h : (G.induce S₂).Reachable ⟨v, hv2⟩ ⟨u, hu⟩ := hs2.1 ⟨v, hv2⟩ ⟨u, hu⟩
    exact h.map (Embedding.induce S₂).toHom
  rw[connected_iff_exists_forall_reachable]
  use v
  intro w
  have hw : w ∈ S₁ ∪ S₂ := by apply hsu
  rcases hw with g | G
  · apply g₁; assumption
  apply g₂; assumption
end SimpleGraph
