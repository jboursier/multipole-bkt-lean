/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeTwoCount.Homogeneous

/-!
# The factorial estimate for homogeneous partitions

The paper: Lemma 5.42.
After the divisibility split, bound the literal factorial quotient. The
exponential series term bounds `q^q/q!` by `e^q`, the elementary Stirling
estimate needed here. No auxiliary parameter is chosen.
-/

@[expose] public section

namespace MultipoleBKT.BadPointTypes.RouteTypeTwoCount

/-- The homogeneous factorial quotient times the block contribution. -/
theorem homogeneous_factorial_bound {n k q : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hsize : k * q = n) {B : ℝ} (hB : 0 ≤ B) :
    (n.factorial : ℝ) / (k.factorial ^ q * q.factorial) * B ^ q ≤
      (n : ℝ) ^ n * (B / n) ^ q * Real.exp 1 ^ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hq : q ≤ n := by nlinarith
  have hkn : (k : ℝ) * q = n := by exact_mod_cast hsize
  have hkf : (k : ℝ) ≤ k.factorial := by exact_mod_cast Nat.self_le_factorial k
  have hf : (0 : ℝ) < k.factorial ^ q * q.factorial := by positivity
  have he : (n : ℝ) ^ q / (k.factorial ^ q * q.factorial) ≤ Real.exp 1 ^ n := by
    calc (n : ℝ) ^ q / (k.factorial ^ q * q.factorial)
        ≤ (n : ℝ) ^ q / ((k : ℝ) ^ q * q.factorial) := by gcongr
      _ = (q : ℝ) ^ q / q.factorial := by rw [← hkn, mul_pow]; field_simp
      _ ≤ Real.exp (q : ℝ) := Real.pow_div_factorial_le_exp (q : ℝ) (by positivity) q
      _ ≤ Real.exp (n : ℝ) := Real.exp_le_exp.2 (by exact_mod_cast hq)
      _ = Real.exp 1 ^ n := by rw [← Real.exp_nat_mul, mul_one]
  have hfac : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  calc (n.factorial : ℝ) / (k.factorial ^ q * q.factorial) * B ^ q =
        (n.factorial : ℝ) * (B / n) ^ q *
          ((n : ℝ) ^ q / (k.factorial ^ q * q.factorial)) := by
          rw [div_pow]
          field_simp
      _ ≤ (n : ℝ) ^ n * (B / n) ^ q * Real.exp 1 ^ n := by
          apply mul_le_mul _ he (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hfac (by positivity)

/-- The paper's homogeneous count estimate, with an explicit universal constant. -/
theorem card_homogeneous_le {α : Type*} [DecidableEq α] (U : Finset α) {k q : ℕ}
    (hk : 1 ≤ k) (hsize : k * q = U.card) (hU : 1 ≤ U.card) :
    ((homogeneous U k).card : ℝ) ≤
      Real.exp 1 ^ U.card * (U.card : ℝ) ^ (U.card - q) := by
  rw [card_homogeneous U hk hsize]
  have h := homogeneous_factorial_bound hU hk hsize (B := (U.card : ℝ)) (by positivity)
  have hn : (0 : ℝ) < U.card := by exact_mod_cast hU
  have hq : q ≤ U.card := by nlinarith
  rw [div_self hn.ne', one_pow, mul_one] at h
  have hpow : (U.card : ℝ) ^ U.card = (U.card : ℝ) ^ (U.card - q) * (U.card : ℝ) ^ q := by
    rw [← pow_add, Nat.sub_add_cancel hq]
  rw [hpow] at h
  have hp : (0 : ℝ) < (U.card : ℝ) ^ q := pow_pos hn _
  apply (mul_le_mul_iff_left₀ hp).1
  calc ((U.card.factorial : ℝ) / (k.factorial ^ q * q.factorial)) * (U.card : ℝ) ^ q
      ≤ ((U.card : ℝ) ^ (U.card - q) * (U.card : ℝ) ^ q) * Real.exp 1 ^ U.card := h
    _ = _ := by ring

end MultipoleBKT.BadPointTypes.RouteTypeTwoCount

end
