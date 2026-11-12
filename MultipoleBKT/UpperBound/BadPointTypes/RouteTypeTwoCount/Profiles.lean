/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.PropFiveFortyFive.Counting
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Explicit size profiles of multipole partitions

The paper: (5.141).
Equal block sizes are collected after labeling the blocks. Thus the factor `1/k₀!`
and the permutations of the size list give `1/∏ m_j!`. The previously proved
finite-set partition count supplies the remaining factorials of the block sizes.
-/

@[expose] public section

namespace MultipoleBKT.BadPointTypes.RouteTypeTwoCount

open Finset SetPartition PropFiveFortyFive

variable {α : Type*} [DecidableEq α]

/-- Size multiplicities of partitions of `n` labels, including the empty profile. -/
noncomputable def profiles (n : ℕ) : Finset (Fin n → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ => range (n + 1)).filter
    fun m => ∑ i : Fin n, ((i : ℕ) + 1) * m i = n

/-- The total number of labels prescribed by a size profile. -/
theorem profiles_total {n : ℕ} {m : Fin n → ℕ} (hm : m ∈ profiles n) :
    ∑ i : Fin n, ((i : ℕ) + 1) * m i = n := by
  classical
  exact (mem_filter.1 hm).2

/-- A size profile has at most `n` components, including when `n = 0`. -/
theorem profiles_components_le {n : ℕ} {m : Fin n → ℕ} (hm : m ∈ profiles n) :
    ∑ i, m i ≤ n := by
  calc ∑ i, m i ≤ ∑ i : Fin n, ((i : ℕ) + 1) * m i :=
        sum_le_sum fun i _ => Nat.le_mul_of_pos_left _ (by omega)
    _ = n := profiles_total hm

/-- All blocks are nonempty and no larger than the ground set. -/
theorem block_sizes {U : Finset α} {π : Finset (Finset α)} (hπ : π ∈ partitions U) :
    ∀ S ∈ π, 1 ≤ S.card ∧ S.card ≤ U.card := by
  intro S hS
  exact ⟨(mem_partitions.1 hπ).1.1 S hS |>.card_pos,
    card_le_card (subset_of_mem_partitions hπ hS)⟩

/-- The total size is the sum of the block sizes. -/
theorem sum_sizes {U : Finset α} {π : Finset (Finset α)} (hπ : π ∈ partitions U) :
    ∑ S ∈ π, S.card = U.card := by
  rw [← (mem_partitions.1 hπ).2, card_biUnion (mem_partitions.1 hπ).1.2]
  rfl

/-- The number of components is at most the number of labels. -/
theorem card_blocks_le {U : Finset α} {π : Finset (Finset α)} (hπ : π ∈ partitions U) :
    π.card ≤ U.card := by
  calc π.card = ∑ _S ∈ π, 1 := by simp
    _ ≤ ∑ S ∈ π, S.card := sum_le_sum fun S hS => (block_sizes hπ S hS).1
    _ = U.card := sum_sizes hπ

/-- Every partition determines a profile of the required total size. -/
theorem mem_profiles {U : Finset α} {π : Finset (Finset α)} (hπ : π ∈ partitions U) :
    blockCount U.card π ∈ profiles U.card := by
  classical
  refine mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => mem_range.2 ?_, ?_⟩
  · exact Nat.lt_succ_of_le ((blockCount_le_card _ _ _).trans (card_blocks_le hπ))
  · rw [sum_mul_blockCount (block_sizes hπ), sum_sizes hπ]

/-- The exact profile count, before factorial cancellation. -/
theorem card_profile_mul (U : Finset α) {m : Fin U.card → ℕ}
    (hm : m ∈ profiles U.card) :
    ((partitions U).filter fun π => blockCount U.card π = m).card * profileWeight m =
      U.card.factorial := by
  classical
  have h := card_partitions_filter_mul U.card U m (profiles_total hm)
  have he : ((partitions U).filter fun π => blockCount U.card π = m) =
      ((partitions U).filter fun π => (∀ S ∈ π, S.card ≤ U.card) ∧ blockCount U.card π = m) := by
    ext π
    simp only [mem_filter]
    exact ⟨fun hπ => ⟨hπ.1, fun S hS => (block_sizes hπ.1 S hS).2, hπ.2⟩,
      fun hπ => ⟨hπ.1, hπ.2.2⟩⟩
  rw [he]
  exact h

/-- (5.141) with equal sizes collected. The denominator consists of the
factorials within each block and the factorials permuting blocks of equal size. -/
theorem sum_partitions_eq_profiles (U : Finset α) (b : ℕ → ℝ) :
    ∑ π ∈ partitions U, ∏ S ∈ π, b S.card =
      (U.card.factorial : ℝ) * ∑ m ∈ profiles U.card,
        ∏ i : Fin U.card, (b ((i : ℕ) + 1) / ((i : ℕ) + 1).factorial) ^ m i /
          (m i).factorial := by
  classical
  rw [← sum_fiberwise_of_maps_to (fun π hπ => mem_profiles hπ), mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hf : ∀ π ∈ (partitions U).filter (fun π => blockCount U.card π = m),
      ∏ S ∈ π, b S.card = ∏ i : Fin U.card, b ((i : ℕ) + 1) ^ m i := by
    intro π hπ
    rw [prod_card_eq_prod_blockCount (block_sizes (mem_filter.1 hπ).1), (mem_filter.1 hπ).2]
  rw [sum_congr rfl hf, sum_const, nsmul_eq_mul]
  have hc : (((partitions U).filter fun π => blockCount U.card π = m).card : ℝ) =
      U.card.factorial / profileWeight m := by
    rw [eq_div_iff (by exact_mod_cast (profileWeight_pos m).ne')]
    exact_mod_cast card_profile_mul U hm
  rw [hc]
  simp only [profileWeight, Nat.cast_prod, Nat.cast_mul, Nat.cast_pow]
  simp_rw [div_pow]
  rw [prod_div_distrib, prod_div_distrib, prod_mul_distrib]
  rw [← div_div]
  ring

/-- First enumerate the number of components, then their sizes. The factor
`k!` inside labels the blocks and the outer `1/k!` forgets those labels.
Equal sizes are collected, giving the factorials of their multiplicities. -/
theorem sum_partitions_eq_component_profiles (U : Finset α) (b : ℕ → ℝ) :
    ∑ π ∈ partitions U, ∏ S ∈ π, b S.card =
      (U.card.factorial : ℝ) * ∑ k ∈ range (U.card + 1),
        1 / (k.factorial : ℝ) *
          ∑ m ∈ (profiles U.card).filter (fun m => ∑ i, m i = k),
            (k.factorial : ℝ) * ∏ i : Fin U.card,
              (b ((i : ℕ) + 1) / ((i : ℕ) + 1).factorial) ^ m i / (m i).factorial := by
  classical
  rw [sum_partitions_eq_profiles]
  congr 1
  rw [← sum_fiberwise_of_maps_to (s := profiles U.card) (t := range (U.card + 1))
    (g := fun m => ∑ i, m i) (fun m hm => mem_range.2 (Nat.lt_succ_of_le (profiles_components_le hm)))]
  apply sum_congr rfl
  intro k _
  rw [← mul_sum, ← mul_assoc, one_div, inv_mul_cancel₀ (by positivity), one_mul]

/-- The multinomial factor permutes a size list with prescribed multiplicities.
This is the passage from labeled block sizes to the collected size profiles. -/
theorem size_list_multinomial {n k : ℕ} (m : Fin n → ℕ) (hm : ∑ i, m i = k) :
    (Nat.multinomial univ m : ℝ) = k.factorial / ∏ i, (m i).factorial := by
  rw [eq_div_iff (by positivity)]
  have h := Nat.multinomial_spec univ m
  rw [hm] at h
  exact_mod_cast (by simpa only [mul_comm] using h)

end MultipoleBKT.BadPointTypes.RouteTypeTwoCount

end
