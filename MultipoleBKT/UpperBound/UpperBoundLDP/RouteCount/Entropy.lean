/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.UpperBoundLDP.RouteCount.Multinomial
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The multinomial entropy estimate

The paper: Proposition 5.38. The factorial form keeps the factor `m! / N^m` until
the outer binomial coefficient is inserted. This permits successive grouping
in (5.115) and (5.132) without paying twice for entropy.
-/

@[expose] public section

namespace MultipoleBKT.UpperBoundLDP.RouteCount

open Finset

/-- The elementary Stirling inequality, including the empty class. -/
theorem pow_le_factorial_exp (n : ℕ) :
    (n : ℝ) ^ n ≤ n.factorial * Real.exp n := by
  simpa only [mul_comm] using (div_le_iff₀ (by positivity : (0 : ℝ) < n.factorial)).1
    (Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n)

/-- The fixed-count entropy estimate with the outer factorial retained.
Multiplication by `binom(N,m)` gives the displayed estimate of the paper. -/
theorem multinomial_entropy_factorial {K m : ℕ} (n : Fin K → ℕ)
    (hn : ∑ j, n j = m) {x : ℝ} (hx : 0 ≤ x) :
    (Nat.multinomial univ n : ℝ) * ∏ j, ((n j : ℝ) * x) ^ n j ≤
      (m.factorial : ℝ) * x ^ m * Real.exp m := by
  have hprod : ∏ j, (n j : ℝ) ^ n j ≤ (∏ j, ((n j).factorial : ℝ)) * Real.exp m := by
    calc ∏ j, (n j : ℝ) ^ n j
        ≤ ∏ j, ((n j).factorial : ℝ) * Real.exp (n j) :=
          prod_le_prod₀ (fun j _ => by positivity) (fun j _ => pow_le_factorial_exp (n j))
      _ = _ := by
        rw [prod_mul_distrib, ← Real.exp_sum]
        congr 2
        exact_mod_cast hn
  have hspec : (Nat.multinomial univ n : ℝ) * ∏ j, ((n j).factorial : ℝ) = m.factorial := by
    exact_mod_cast (show Nat.multinomial univ n * ∏ j, (n j).factorial = m.factorial by
      rw [mul_comm, Nat.multinomial_spec, hn])
  simp_rw [mul_pow]
  rw [prod_mul_distrib, prod_pow_eq_pow_sum, hn]
  calc (Nat.multinomial univ n : ℝ) * ((∏ j, (n j : ℝ) ^ n j) * x ^ m)
      ≤ (Nat.multinomial univ n : ℝ) *
          (((∏ j, ((n j).factorial : ℝ)) * Real.exp m) * x ^ m) := by gcongr
    _ = _ := by rw [← mul_assoc, ← mul_assoc, hspec]; ring

/-- The remaining binomial coefficient cancels `m! / N^m`. -/
theorem choose_factorial_le {N m : ℕ} (hN : 1 ≤ N) :
    (N.choose m : ℝ) * (m.factorial * (1 / (N : ℝ)) ^ m) ≤ 1 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  calc (N.choose m : ℝ) * (m.factorial * (1 / (N : ℝ)) ^ m)
      ≤ ((N : ℝ) ^ m / m.factorial) * (m.factorial * (1 / (N : ℝ)) ^ m) :=
        mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div m N) (by positivity)
    _ = 1 := by
      field_simp
      rw [← mul_pow]
      simp [hN0.ne']

/-- The displayed entropy inequality of Proposition 5.38, with all zero counts allowed. -/
theorem multinomial_entropy {K N m : ℕ} (hN : 1 ≤ N) (n : Fin K → ℕ)
    (hn : ∑ j, n j = m) :
    (N.choose m : ℝ) * ((m.factorial : ℝ) / ∏ j, ((n j).factorial : ℝ)) ≤
      Real.exp m * ∏ j, ((N : ℝ) / n j) ^ n j := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : 0 < ∏ j, ((n j : ℝ) / N) ^ n j := prod_pos fun j _ => by
    rcases Nat.eq_zero_or_pos (n j) with he | he
    · simp [he]
    · exact pow_pos (div_pos (by exact_mod_cast he) hN0) _
  have hspec : (m.factorial : ℝ) / ∏ j, ((n j).factorial : ℝ) = Nat.multinomial univ n := by
    rw [div_eq_iff (by positivity)]
    exact_mod_cast (show m.factorial = Nat.multinomial univ n * ∏ j, (n j).factorial by
      rw [mul_comm, Nat.multinomial_spec, hn])
  rw [hspec]
  apply (mul_le_mul_iff_right₀ hpos).1
  have hinv : (∏ j, ((n j : ℝ) / N) ^ n j) * (∏ j, ((N : ℝ) / n j) ^ n j) = 1 := by
    rw [← prod_mul_distrib]
    apply prod_eq_one
    intro j _
    rcases Nat.eq_zero_or_pos (n j) with he | he
    · simp [he]
    · rw [← mul_pow]
      have hn0 : (n j : ℝ) ≠ 0 := by exact_mod_cast he.ne'
      field_simp
      rw [one_pow]
  calc (∏ j, ((n j : ℝ) / N) ^ n j) * ((N.choose m : ℝ) * Nat.multinomial univ n)
      = (N.choose m : ℝ) *
          ((Nat.multinomial univ n : ℝ) * ∏ j, ((n j : ℝ) * (1 / N)) ^ n j) := by
        simp only [div_eq_mul_inv, one_mul, mul_pow, prod_mul_distrib]; ring
    _ ≤ (N.choose m : ℝ) * ((m.factorial : ℝ) * (1 / N) ^ m * Real.exp m) :=
      mul_le_mul_of_nonneg_left (multinomial_entropy_factorial n hn (by positivity)) (by positivity)
    _ ≤ 1 * Real.exp m := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (choose_factorial_le hN) (Real.exp_pos _).le
    _ = (∏ j, ((n j : ℝ) / N) ^ n j) * (Real.exp m * ∏ j, ((N : ℝ) / n j) ^ n j) := by
      rw [mul_left_comm, hinv, mul_one, one_mul]

end MultipoleBKT.UpperBoundLDP.RouteCount

end
