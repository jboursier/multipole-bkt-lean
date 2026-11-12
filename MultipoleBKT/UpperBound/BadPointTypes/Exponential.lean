/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeTwoCount.Profiles

/-!
# The written exponential summation

The paper: (5.141) and the
following exponential series. Sum the explicit size profiles
with factorial denominators and recognize the exponential series.
-/

@[expose] public section

namespace MultipoleBKT.BadPointTypes.RouteTypeTwoCount

open Finset SetPartition PropFiveFortyFive

variable {α : Type*} [DecidableEq α]

/-- Summation of the explicit factorial denominators is the exponential series.
The fixed-total-size constraint is dropped only after the partition count. -/
theorem sum_partitions_le_exp (U : Finset α) {b : ℕ → ℝ} (hb : ∀ m, 0 ≤ b m)
    {y : ℝ} (hy : 0 < y) :
    ∑ π ∈ partitions U, ∏ S ∈ π, b S.card ≤
      U.card.factorial / y ^ U.card *
        Real.exp (∑ m ∈ range U.card, b (m + 1) / (m + 1).factorial * y ^ (m + 1)) := by
  classical
  let a : Fin U.card → ℝ := fun i => b ((i : ℕ) + 1) / ((i : ℕ) + 1).factorial *
    y ^ ((i : ℕ) + 1)
  have ha : ∀ i, 0 ≤ a i := fun i => mul_nonneg (div_nonneg (hb _) (by positivity)) (pow_nonneg hy.le _)
  have ht : ∀ m ∈ profiles U.card,
      (∏ i : Fin U.card, (b ((i : ℕ) + 1) / ((i : ℕ) + 1).factorial) ^ m i /
          (m i).factorial) * y ^ U.card = ∏ i, a i ^ m i / (m i).factorial := by
    intro m hm
    have hmass := profiles_total hm
    conv_lhs => arg 2; rw [← hmass]
    rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
    apply prod_congr rfl
    intro i _
    dsimp [a]
    rw [mul_pow, pow_mul]
    ring
  have hinner (k : ℕ) :
      (∑ m ∈ (profiles U.card).filter (fun m => ∑ i, m i = k),
        (k.factorial : ℝ) * ∏ i, a i ^ m i / (m i).factorial) ≤ (∑ i, a i) ^ k := by
    have he : ∀ m ∈ (profiles U.card).filter (fun m => ∑ i, m i = k),
        (k.factorial : ℝ) * (∏ i, a i ^ m i / (m i).factorial) =
          (Nat.multinomial univ m : ℝ) * ∏ i, a i ^ m i := by
      intro m hm
      rw [size_list_multinomial m (mem_filter.1 hm).2, prod_div_distrib, Nat.cast_prod]
      ring
    rw [sum_congr rfl he, sum_pow_eq_sum_piAntidiag]
    apply sum_le_sum_of_subset_of_nonneg
    · intro m hm
      exact mem_piAntidiag.2 ⟨(mem_filter.1 hm).2, fun _ _ => mem_univ _⟩
    · intro m _ _
      exact mul_nonneg (Nat.cast_nonneg _) (prod_nonneg fun i _ => pow_nonneg (ha i) _)
  rw [sum_partitions_eq_component_profiles]
  have hsum : (∑ k ∈ range (U.card + 1), 1 / (k.factorial : ℝ) *
      ∑ m ∈ (profiles U.card).filter (fun m => ∑ i, m i = k),
        (k.factorial : ℝ) * ∏ i : Fin U.card,
          (b ((i : ℕ) + 1) / ((i : ℕ) + 1).factorial) ^ m i / (m i).factorial) *
        y ^ U.card ≤ Real.exp (∑ i, a i) := by
    calc _ = ∑ k ∈ range (U.card + 1), 1 / (k.factorial : ℝ) *
          ∑ m ∈ (profiles U.card).filter (fun m => ∑ i, m i = k),
            (k.factorial : ℝ) * ∏ i, a i ^ m i / (m i).factorial := by
          rw [sum_mul]
          apply sum_congr rfl
          intro k _
          rw [mul_assoc, sum_mul]
          apply congrArg ((1 / (k.factorial : ℝ)) * ·)
          apply sum_congr rfl
          intro m hm
          rw [mul_assoc, ht m (mem_filter.1 hm).1]
      _ ≤ ∑ k ∈ range (U.card + 1), (∑ i, a i) ^ k / k.factorial := by
          apply sum_le_sum
          intro k _
          simpa only [one_div, mul_comm, div_eq_mul_inv, mul_one] using
            mul_le_mul_of_nonneg_left (hinner k) (show 0 ≤ 1 / (k.factorial : ℝ) by positivity)
      _ ≤ Real.exp (∑ i, a i) :=
          Real.sum_le_exp_of_nonneg (sum_nonneg fun i _ => ha i) _
  have hfinal : Real.exp (∑ i, a i) =
      Real.exp (∑ m ∈ range U.card, b (m + 1) / (m + 1).factorial * y ^ (m + 1)) := by
    dsimp [a]
    rw [sum_range]
  rw [hfinal] at hsum
  have hy0 : 0 < y ^ U.card := pow_pos hy _
  rw [div_mul_eq_mul_div, le_div_iff₀ hy0]
  nlinarith [mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ U.card.factorial by positivity)]

end MultipoleBKT.BadPointTypes.RouteTypeTwoCount

end
