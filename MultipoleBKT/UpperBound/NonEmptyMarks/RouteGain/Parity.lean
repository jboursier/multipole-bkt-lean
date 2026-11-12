/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.NonEmptyMarks.RouteGain.Separation

/-!
# The isolated marked multipole case

The paper: (5.106). If every marked vertex lies outside the nontrivial odd
components, its multipole has no incident odd edge. Block parity then
gives two distinct marks. Erasing both preserves the parity condition.
-/

public section

namespace MultipoleBKT.UpperBound.NonEmptyMarks

open Finset SimpleGraph Hierarchical Multipole Parity BoundedUpper SetPartition
open scoped Classical

/-! ### Combinatorics of the marks -/

section Marks

variable {X : Finset (Finset ℕ)}

/-- An edge of `E₁` touching a block `S` puts `S` in an odd component of `E₁`. -/
theorem mem_oddComponents_of_edge {E₁ : Finset (ℕ × ℕ)} (hE₁ : E₁ ⊆ interPairs X)
    {p : ℕ × ℕ} (hp : p ∈ E₁) {S : Finset ℕ} (hS : S ∈ X) (hpS : p.1 ∈ S ∨ p.2 ∈ S) :
    reachedBlocks X E₁ p.1 ∈ oddComponents X E₁ ∧ S ∈ reachedBlocks X E₁ p.1 := by
  obtain ⟨B, hB, B', hB', hBB', h1, h2⟩ := exists_of_mem_interPairs (hE₁ hp)
  have hlt := (mem_pairsOn.1 (interPairs_subset_pairsOn (hE₁ hp))).2.2
  have hadj : (edgeGraph (E₁ ∪ intraPairs X)).Reachable p.1 p.2 :=
    SimpleGraph.Adj.reachable (edgeGraph_adj.2 ⟨hlt.ne, Or.inl (Finset.mem_union_left _ hp)⟩)
  have hBm : B ∈ reachedBlocks X E₁ p.1 := mem_reachedBlocks_self hB h1
  have hB'm : B' ∈ reachedBlocks X E₁ p.1 :=
    BoundedUpper.mem_reachedBlocks_iff.2 ⟨hB', p.2, h2, hadj⟩
  refine ⟨mem_oddComponents.2 ⟨mem_relComponents.2 ⟨p.1, mem_biUnion_id.2 ⟨B, hB, h1⟩, rfl⟩,
    Finset.one_lt_card.2 ⟨B, hBm, B', hB'm, hBB'⟩⟩, ?_⟩
  rcases hpS with h | h
  · exact mem_reachedBlocks_self hS h
  · exact BoundedUpper.mem_reachedBlocks_iff.2 ⟨hS, p.2, h, hadj⟩

/-- **Two marks in one block keep the parity**: removing two marks `i₁ ≠ i₂` of the same block
`S ∈ X` from `U` preserves `E₁ ∈ Eul^X(U)`. -/
theorem isParityPair_erase_two (hX : IsSubpartition X) {E₁ : Finset (ℕ × ℕ)} {U : Finset ℕ}
    (hpar : IsParityPair X E₁ U) {S : Finset ℕ} (hS : S ∈ X) {i₁ i₂ : ℕ} (h1 : i₁ ∈ S ∩ U)
    (h2 : i₂ ∈ S ∩ U) (h12 : i₁ ≠ i₂) : IsParityPair X E₁ ((U.erase i₁).erase i₂) := by
  intro S' hS'
  have hp := hpar S' hS'
  by_cases hSS : S' = S
  · subst hSS
    have hc : (S' ∩ (U.erase i₁).erase i₂).card + 2 = (S' ∩ U).card := by
      rw [Finset.inter_erase, Finset.inter_erase, Finset.card_erase_of_mem
        (Finset.mem_erase.2 ⟨Ne.symm h12, h2⟩), Finset.card_erase_of_mem h1]
      have : 2 ≤ (S' ∩ U).card := by
        rw [← Finset.card_pair h12]
        exact Finset.card_le_card (by
          intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact h1
          · rw [Finset.mem_singleton.1 hx]; exact h2)
      omega
    rw [← hc, ← add_assoc] at hp
    obtain ⟨r, hr⟩ := hp
    exact ⟨r - 1, by omega⟩
  · have hi₁ : i₁ ∉ S' := fun h => hSS (eq_of_isSubpartition hX hS' hS h (Finset.mem_inter.1 h1).1)
    have hi₂ : i₂ ∉ S' := fun h => hSS (eq_of_isSubpartition hX hS' hS h (Finset.mem_inter.1 h2).1)
    have : S' ∩ (U.erase i₁).erase i₂ = S' ∩ U := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_erase]
      constructor
      · rintro ⟨hx, -, -, hxU⟩
        exact ⟨hx, hxU⟩
      · rintro ⟨hx, hxU⟩
        exact ⟨hx, fun h => hi₂ (h ▸ hx), fun h => hi₁ (h ▸ hx), hxU⟩
    rw [this]
    exact hp

/-- If no odd component meets the nonempty set of odd marks, a marked
multipole has degree zero and contains two distinct marks.
The paper: (5.106). -/
theorem isolated_mark_pair {E₁ : Finset (ℕ × ℕ)}
    (hE₁X : E₁ ⊆ interPairs X) {U : Finset ℕ} (hU : U ⊆ X.biUnion id)
    (hUne : U.Nonempty) (hpar : IsParityPair X E₁ U)
    (hno : ¬ ∃ Y ∈ oddComponents X E₁, (U ∩ Y.biUnion id).Nonempty) :
    ∃ S ∈ X, blockDeg E₁ S = 0 ∧
      ∃ i ∈ S ∩ U, ∃ j ∈ S ∩ U, i ≠ j := by
  obtain ⟨i, hi⟩ := hUne
  obtain ⟨S, hS, hiS⟩ := mem_biUnion_id.1 (hU hi)
  have hdeg : blockDeg E₁ S = 0 := by
    unfold blockDeg
    have key : ∀ p ∈ E₁, ¬ (p.1 ∈ S ∨ p.2 ∈ S) := by
      intro p hp hpS
      obtain ⟨hY, hSY⟩ := mem_oddComponents_of_edge hE₁X hp hS hpS
      exact hno ⟨_, hY, i, Finset.mem_inter.2 ⟨hi, mem_biUnion_id.2 ⟨S, hSY, hiS⟩⟩⟩
    rw [Finset.filter_false_of_mem fun p hp h => key p hp (Or.inl h),
      Finset.filter_false_of_mem fun p hp h => key p hp (Or.inr h), Finset.card_empty]
  have hpS := hpar S hS
  rw [hdeg, zero_add] at hpS
  have hiSU : i ∈ S ∩ U := Finset.mem_inter.2 ⟨hiS, hi⟩
  obtain ⟨j, hj, hji⟩ : ∃ j ∈ S ∩ U, j ≠ i := by
    by_contra hno
    push Not at hno
    have h1 : (S ∩ U).card = 1 :=
      Finset.card_eq_one.2 ⟨i, Finset.eq_singleton_iff_unique_mem.2 ⟨hiSU, hno⟩⟩
    rw [h1] at hpS
    exact Nat.not_even_one hpS
  exact ⟨S, hS, hdeg, i, hiSU, j, hj, hji.symm⟩

end Marks

end MultipoleBKT.UpperBound.NonEmptyMarks

end
