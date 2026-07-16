import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank

variable {k V P : Type*} [Field k] [AddCommGroup V] [Module k V] [AddTorsor V P]

-- The dimension of the affine span of a finite set of points is at most its cardinality minus 1.
lemma affineSpan_dim_le_card_sub_one (s : Finset P) :
  Module.finrank k (affineSpan k (s : Set P)).direction ≤ s.card - 1 := by
  classical
  rcases Finset.eq_empty_or_nonempty s with rfl | ⟨p, hp⟩
  · rw [Finset.coe_empty]
    rw [Nat.sub_eq_max_sub]
    refine Nat.le_sub_one_of_lt ?_
    rw [AffineSubspace.span_empty]
    rw [AffineSubspace.direction_bot]
    simp
  · rw [Nat.sub_one]
    let s_vec := (s.erase p).image (fun x ↦ x -ᵥ p)
    have h_span : vectorSpan k (s : Set P) ≤ Submodule.span k (s_vec : Set V) := by
      rw [vectorSpan_def]
      rw [Submodule.span_le]
      rintro v ⟨q, hq, r, hr, rfl⟩
      have h_sub : q -ᵥ r = (q -ᵥ p) - (r -ᵥ p) := by exact (vsub_sub_vsub_cancel_right q r p).symm
      dsimp only
      rw [h_sub]
      apply sub_mem
      · by_cases h_eq : q = p
        · rw [h_eq, vsub_self]
          exact Submodule.zero_mem _
        · apply Submodule.subset_span
          simp only [s_vec, Finset.mem_coe, Finset.mem_image, Finset.mem_erase]
          exact ⟨q, ⟨h_eq, hq⟩, rfl⟩
      · by_cases h_eq : r = p
        · rw [h_eq, vsub_self]
          exact Submodule.zero_mem _
        · apply Submodule.subset_span
          simp only [s_vec, Finset.mem_coe, Finset.mem_image, Finset.mem_erase]
          exact ⟨r, ⟨h_eq, hr⟩, rfl⟩
    have h_dim1 := Submodule.finrank_mono h_span
    have h_dim2 : Module.finrank k (Submodule.span k (s_vec : Set V)) ≤ s_vec.card :=
      finrank_span_finset_le_card s_vec
    have h_dim3 : s_vec.card ≤ s.card - 1 := by
      have h_card_vec : s_vec.card ≤ (s.erase p).card := Finset.card_image_le
      have h_card_erase : (s.erase p).card = s.card - 1 := Finset.card_erase_of_mem hp
      rw [h_card_erase] at h_card_vec
      exact h_card_vec
    rw [direction_affineSpan]
    exact le_trans h_dim1 (le_trans h_dim2 h_dim3)
