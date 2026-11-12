/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.TypeOneIntegral
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Same-sign partitions in the successive type-1 enumeration

The paper: Lemma 5.40,
(5.127) and Step 6.
A partition is represented by its retraction onto a chosen representative in each block.
Counting these rooted partitions also bounds the paper's unrooted partitions. For fixed
representatives, every other label chooses its representative. Choosing the representatives
first supplies the factorial denominator for the number of blocks.
-/

@[expose] public section

namespace MultipoleBKT.BadPointTypes.RouteTypeOne

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

open scoped Classical in
/-- Representatives of the blocks of a retraction on `A`. -/
noncomputable def roots (A : Finset α) (p : α → α) : Finset α :=
  A.filter fun i => p i = i

/-- A same-sign partition, with one representative in each block. All blocks have size
one or `q + 1`. The map is the identity off its ground set. -/
def IsPartition (q : ℕ) (A : Finset α) (p : α → α) : Prop :=
  (∀ i ∉ A, p i = i) ∧ (∀ i ∈ A, p i ∈ A ∧ p (p i) = p i) ∧
    ∀ r ∈ roots A p, (A.filter fun i => p i = r).card = 1 ∨
      (A.filter fun i => p i = r).card = q + 1

open scoped Classical in
/-- The finite set of same-sign partitions with `k` blocks. -/
noncomputable def partitions (q : ℕ) (A : Finset α) (k : ℕ) : Finset (α → α) :=
  univ.filter fun p => IsPartition q A p ∧ (roots A p).card = k

/-- For fixed representatives, each remaining label chooses a representative. -/
theorem card_partition_fiber_le (q : ℕ) (A R : Finset α) (k : ℕ)
    (hR : R ∈ A.powersetCard k) :
    ((partitions q A k).filter fun p => roots A p = R).card ≤ k ^ (A.card - k) := by
  classical
  obtain ⟨hRA, hRk⟩ := mem_powersetCard.1 hR
  let choices := Fintype.piFinset fun i => if i ∈ A \ R then R else {i}
  have hsub : ((partitions q A k).filter fun p => roots A p = R) ⊆ choices := by
    intro p hp
    obtain ⟨hp, he⟩ := mem_filter.1 hp
    obtain ⟨hP, -⟩ := (mem_filter.1 hp).2
    refine Fintype.mem_piFinset.2 fun i => ?_
    by_cases hi : i ∈ A \ R
    · rw [ite_eq_left hi]
      rw [← he, roots, mem_filter]
      exact hP.2.1 i (mem_sdiff.1 hi).1
    · rw [ite_eq_right hi, mem_singleton]
      by_cases hiA : i ∈ A
      · have hiR : i ∈ R := by simpa [mem_sdiff, hiA] using hi
        rw [← he, roots, mem_filter] at hiR
        exact hiR.2
      · exact hP.1 i hiA
  refine (card_le_card hsub).trans_eq ?_
  rw [Fintype.card_piFinset]
  simp only [apply_ite Finset.card, card_singleton, hRk]
  rw [prod_ite, prod_const, prod_const_one, mul_one]
  congr 1
  rw [filter_mem_eq_inter, univ_inter, card_sdiff_of_subset hRA, hRk]

/-- The paper's partition count, with distinguished representatives included. -/
theorem card_partitions_le (q : ℕ) (A : Finset α) (k : ℕ) :
    (partitions q A k).card ≤ A.card.choose k * k ^ (A.card - k) := by
  classical
  have hmap : ∀ p ∈ partitions q A k, roots A p ∈ A.powersetCard k := by
    intro p hp
    exact mem_powersetCard.2 ⟨filter_subset _ _, (mem_filter.1 hp).2.2⟩
  rw [card_eq_sum_card_fiberwise hmap]
  calc ∑ R ∈ A.powersetCard k, ((partitions q A k).filter fun p => roots A p = R).card
      ≤ ∑ _R ∈ A.powersetCard k, k ^ (A.card - k) :=
        sum_le_sum fun R hR => card_partition_fiber_le q A R k hR
    _ = A.card.choose k * k ^ (A.card - k) := by
      simp only [sum_const, nsmul_eq_mul, card_powersetCard, Nat.cast_id]

/-- Multiplying the partition count by `k!` costs at most `|A|^{|A|}`.
This is the partition estimate used in Step 6, including the empty ground set. -/
theorem card_partitions_mul_factorial_le (q : ℕ) (A : Finset α) (k : ℕ) :
    (partitions q A k).card * k.factorial ≤ A.card ^ A.card := by
  by_cases hk : k ≤ A.card
  · calc (partitions q A k).card * k.factorial
        ≤ (A.card.choose k * k ^ (A.card - k)) * k.factorial :=
          Nat.mul_le_mul_right _ (card_partitions_le q A k)
      _ = A.card.descFactorial k * k ^ (A.card - k) := by
        rw [Nat.descFactorial_eq_factorial_mul_choose]
        ring
      _ ≤ A.card ^ k * A.card ^ (A.card - k) :=
        Nat.mul_le_mul (Nat.descFactorial_le_pow _ _) (Nat.pow_le_pow_left hk _)
      _ = A.card ^ A.card := by rw [← pow_add, Nat.add_sub_of_le hk]
  · have hz : A.card.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have hc := card_partitions_le q A k
    rw [hz, zero_mul] at hc
    rw [Nat.eq_zero_of_le_zero hc, zero_mul]
    exact Nat.zero_le _

/-- The real-valued form of the stated `|A|^{|A|}/k!` estimate. -/
theorem card_partitions_le_div (q : ℕ) (A : Finset α) (k : ℕ) :
    ((partitions q A k).card : ℝ) ≤ (A.card : ℝ) ^ A.card / k.factorial := by
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < k.factorial)]
  exact_mod_cast card_partitions_mul_factorial_le q A k

end MultipoleBKT.BadPointTypes.RouteTypeOne

end
