/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.UpperBoundLDP.RouteCount.Entropy

/-!
# Absorbing the class counts

The paper: Proposition 5.38. First group labellings by counts. The multinomial cancels
the class factorials. There are at most `K^m` count vectors for `K` classes.
The factorial form allows the two splits in the paper to be applied successively.
-/

@[expose] public section

namespace MultipoleBKT.UpperBoundLDP.RouteCount

open Finset
open scoped ENNReal

/-- The coarse count of class-count vectors used in the two maxima in the paper. -/
theorem card_profiles_le (m K : ℕ) :
    (piAntidiag (univ : Finset (Fin K)) m).card ≤ K ^ m := by
  have h := sum_counts (m := m) (K := K) (R := ℕ) (fun _ => 1)
  simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul,
    mul_one] at h
  calc (piAntidiag (univ : Finset (Fin K)) m).card
      = ∑ _n ∈ piAntidiag (univ : Finset (Fin K)) m, 1 := by simp
    _ ≤ ∑ n ∈ piAntidiag (univ : Finset (Fin K)) m, Nat.multinomial univ n :=
      sum_le_sum fun n _ => (Nat.multinomial_pos (s := univ) (f := n))
    _ = K ^ m := h.symm

/-- Bound the sum after fixing each class-count vector. -/
theorem sum_counts_le {m K : ℕ} {B : ℝ} (hB : 0 ≤ B)
    {Z : Fin K → ℕ → ℝ≥0∞}
    (hterm : ∀ n ∈ piAntidiag (univ : Finset (Fin K)) m,
      (Nat.multinomial univ n : ℝ≥0∞) * ∏ j, Z j (n j) ≤ ENNReal.ofReal B) :
    ∑ f : Fin m → Fin K, ∏ j, Z j (fiber f j).card ≤ ENNReal.ofReal ((K : ℝ) ^ m * B) := by
  classical
  rw [show (∑ f : Fin m → Fin K, ∏ j, Z j (fiber f j).card) =
      ∑ n ∈ piAntidiag (univ : Finset (Fin K)) m,
        (Nat.multinomial univ n : ℝ≥0∞) * ∏ j, Z j (n j) from
    sum_counts (fun n => ∏ j, Z j (n j))]
  refine (sum_le_sum fun n hn => hterm n hn).trans ?_
  rw [sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (by exact_mod_cast card_profiles_le m K) hB)

/-- Sum factorial-normalized class bounds after grouping by their counts. -/
theorem sum_factorial_le {m K : ℕ} {A x w : ℝ}
    (hA : 0 ≤ A) (hx : 0 ≤ x) (hw : 0 ≤ w) {E : Fin K → ℝ}
    (hE : ∀ j, 0 ≤ E j) {Z : Fin K → ℕ → ℝ≥0∞}
    (hZ : ∀ j n, n ≤ m → Z j n ≤
      ENNReal.ofReal (A ^ n * (n.factorial * x ^ n) * w ^ n * E j)) :
    ∑ f : Fin m → Fin K, ∏ j, Z j (fiber f j).card ≤
      ENNReal.ofReal (A ^ m * (m.factorial * x ^ m) * (K * w) ^ m * ∏ j, E j) := by
  classical
  have hterm : ∀ n ∈ piAntidiag (univ : Finset (Fin K)) m,
      (Nat.multinomial univ n : ℝ≥0∞) * ∏ j, Z j (n j) ≤
        ENNReal.ofReal (A ^ m * (m.factorial * x ^ m) * w ^ m * ∏ j, E j) := by
    intro n hn
    have hsum := (mem_piAntidiag.1 hn).1
    have hle (j : Fin K) : n j ≤ m := hsum ▸ single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ j)
    calc (Nat.multinomial univ n : ℝ≥0∞) * ∏ j, Z j (n j)
        ≤ ENNReal.ofReal (Nat.multinomial univ n : ℝ) *
            ∏ j, ENNReal.ofReal (A ^ n j * ((n j).factorial * x ^ n j) * w ^ n j * E j) := by
          rw [ENNReal.ofReal_natCast]
          gcongr with j
          exact hZ j _ (hle j)
      _ = _ := by
        rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => by have := hE j; positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp_rw [prod_mul_distrib]
        rw [prod_pow_eq_pow_sum, prod_pow_eq_pow_sum, prod_pow_eq_pow_sum, hsum]
        have hspec : (Nat.multinomial univ n : ℝ) * ∏ j, ((n j).factorial : ℝ) = m.factorial := by
          exact_mod_cast (show Nat.multinomial univ n * ∏ j, (n j).factorial = m.factorial by
            rw [mul_comm, Nat.multinomial_spec, hsum])
        calc (Nat.multinomial univ n : ℝ) *
            (A ^ m * ((∏ j, ((n j).factorial : ℝ)) * x ^ m) * w ^ m * ∏ j, E j)
            = A ^ m * (((Nat.multinomial univ n : ℝ) * ∏ j, ((n j).factorial : ℝ)) *
                x ^ m) * w ^ m * ∏ j, E j := by ring
          _ = _ := by rw [hspec]
  have hEprod : 0 ≤ ∏ j, E j := prod_nonneg (fun j _ => hE j)
  refine (sum_counts_le (by positivity) hterm).trans (le_of_eq ?_)
  congr 1
  rw [mul_pow]
  ring

/-- Cancellation of the individual class normalizations by the entropy inequality.
The factor `m!` is retained for the outer binomial coefficient. -/
theorem power_normalization_le_factorial {A x w E : ℝ} (hA : 0 ≤ A) (hx : 0 ≤ x)
    (hw : 0 ≤ w) (hE : 0 ≤ E) (n : ℕ) :
    A ^ n * ((n : ℝ) * x) ^ n * w ^ n * E ≤
      A ^ n * (n.factorial * x ^ n) * (Real.exp 1 * w) ^ n * E := by
  have he : Real.exp (n : ℝ) = Real.exp 1 ^ n := by rw [← Real.exp_nat_mul, mul_one]
  have hnj := pow_le_factorial_exp n
  rw [he] at hnj
  calc A ^ n * ((n : ℝ) * x) ^ n * w ^ n * E
      = A ^ n * ((n : ℝ) ^ n * x ^ n) * w ^ n * E := by rw [mul_pow]
    _ ≤ A ^ n * ((n.factorial * Real.exp 1 ^ n) * x ^ n) * w ^ n * E := by gcongr
    _ = _ := by rw [mul_pow]; ring

/-- Entropy absorption for a sum over labellings, retaining the outer factorial. -/
theorem sum_entropy_le {m K : ℕ} {A x w : ℝ}
    (hA : 0 ≤ A) (hx : 0 ≤ x) (hw : 0 ≤ w) {E : Fin K → ℝ}
    (hE : ∀ j, 0 ≤ E j) {Z : Fin K → ℕ → ℝ≥0∞}
    (hZ : ∀ j n, n ≤ m → Z j n ≤
      ENNReal.ofReal (A ^ n * ((n : ℝ) * x) ^ n * w ^ n * E j)) :
    ∑ f : Fin m → Fin K, ∏ j, Z j (fiber f j).card ≤
      ENNReal.ofReal (A ^ m * (m.factorial * x ^ m) *
        (K * (Real.exp 1 * w)) ^ m * ∏ j, E j) := by
  classical
  have hterm : ∀ n ∈ piAntidiag (univ : Finset (Fin K)) m,
      (Nat.multinomial univ n : ℝ≥0∞) * ∏ j, Z j (n j) ≤
        ENNReal.ofReal (A ^ m * (m.factorial * x ^ m) *
          (Real.exp 1 * w) ^ m * ∏ j, E j) := by
    intro n hn
    have hsum := (mem_piAntidiag.1 hn).1
    have hle (j : Fin K) : n j ≤ m := hsum ▸ single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ j)
    calc (Nat.multinomial univ n : ℝ≥0∞) * ∏ j, Z j (n j)
        ≤ ENNReal.ofReal (Nat.multinomial univ n : ℝ) *
            ∏ j, ENNReal.ofReal (A ^ n j * ((n j : ℝ) * x) ^ n j * w ^ n j * E j) := by
          rw [ENNReal.ofReal_natCast]
          gcongr with j
          exact hZ j _ (hle j)
      _ = ENNReal.ofReal (A ^ m * w ^ m * (∏ j, E j) *
          ((Nat.multinomial univ n : ℝ) * ∏ j, ((n j : ℝ) * x) ^ n j)) := by
        rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => by have := hE j; positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp_rw [prod_mul_distrib]
        rw [prod_pow_eq_pow_sum, prod_pow_eq_pow_sum, hsum]
        ring
      _ ≤ ENNReal.ofReal (A ^ m * w ^ m * (∏ j, E j) *
          (m.factorial * x ^ m * Real.exp m)) := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left (multinomial_entropy_factorial n hsum hx)
        exact mul_nonneg (mul_nonneg (pow_nonneg hA _) (pow_nonneg hw _))
          (prod_nonneg (fun j _ => hE j))
      _ = _ := by
        rw [show Real.exp (m : ℝ) = Real.exp 1 ^ m by rw [← Real.exp_nat_mul, mul_one]]
        congr 1
        rw [mul_pow]
        ring
  have hEprod : 0 ≤ ∏ j, E j := prod_nonneg (fun j _ => hE j)
  refine (sum_counts_le (by positivity) hterm).trans (le_of_eq ?_)
  congr 1
  rw [mul_pow]
  ring

end MultipoleBKT.UpperBoundLDP.RouteCount

end
