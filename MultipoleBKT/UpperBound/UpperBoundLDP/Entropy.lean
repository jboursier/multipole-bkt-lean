/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.PropFiveFortyFive.Goal
public import MultipoleBKT.Main.TheoremTwo.Parameters
public import TwoComponentCoulomb.Integrals.Stirling

/-!
# Proposition 5.43, Steps 1 and 3: Stirling's formula and the rate function

The paper: proof of Proposition 5.43, eq.
(5.144) and Step 3. For a profile `n` with
`N' = ∑ₖ k n_k ≤ N` and `m = ∑ₖ n_k`, `γ = n/N`:

  `log (N'!/∏ₖ (k!)^{n_k} n_k!) + ∑ₖ n_k log 𝗆(k) - (N' - m) log N - N h(γ) - (N - N')
    ≤ -N ℐ(γ) + 1 + log N`

(`log_profile_le`), from `log n_k! ≥ n_k log n_k - n_k`, `log N'! ≤ N' log N' - N' + 1 + log N'`
and `N' ≤ N` (the paper's `(N'/N)^{N'} e^{-N'} ≤ e^{-N} e^{|V_bad|}`, eq. (5.144)); here
`h` is the cluster part of the rate function (`MultipoleBKT.rateCluster`).

-/

@[expose] public section

open Finset

namespace MultipoleBKT

namespace UpperBoundLDP

open PropFiveFortyFive

/-- `k log k - k ≤ log k!` for every `k`. -/
theorem log_factorial_ge' (k : ℕ) : (k : ℝ) * Real.log k - k ≤ Real.log (k.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have := TwoComponentCoulomb.log_factorial_ge hk
    linarith

/-- `log N'! ≤ N' log N - N' + 1 + log N` for `N' ≤ N`, `N ≥ 1`. -/
theorem log_factorial_le_of_le {N' N : ℕ} (hN : 1 ≤ N) (h : N' ≤ N) :
    Real.log (N'.factorial : ℝ) ≤ (N' : ℝ) * Real.log N - N' + 1 + Real.log N := by
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  rcases Nat.eq_zero_or_pos N' with rfl | hN'
  · simp only [Nat.factorial_zero, Nat.cast_one, Real.log_one, Nat.cast_zero, zero_mul, sub_zero,
      zero_add]
    linarith
  · have h1 := TheoremTwo.log_factorial_le hN'
    have hN'0 : (0 : ℝ) < N' := by exact_mod_cast hN'
    have h2 : Real.log N' ≤ Real.log N := Real.log_le_log hN'0 (by exact_mod_cast h)
    have h3 : (N' : ℝ) * Real.log N' ≤ N' * Real.log N := mul_le_mul_of_nonneg_left h2 hN'0.le
    linarith

/-- **The entropy bound** (eq. (5.144) and Step 3, see the module docstring). -/
theorem log_profile_le {p N : ℕ} (hN : 1 ≤ N) (n : Fin p → ℕ)
    (hn : ∑ i : Fin p, ((i : ℕ) + 1) * n i ≤ N) (msf : ℕ → ℝ) (kmult : (ℕ →₀ ℕ) → ℝ) :
    Real.log (((∑ i : Fin p, ((i : ℕ) + 1) * n i).factorial : ℝ) / profileWeight n) +
        ∑ i, (n i : ℝ) * Real.log (msf ((i : ℕ) + 1)) -
        ((∑ i : Fin p, ((i : ℕ) + 1) * n i : ℕ) - (∑ i, n i : ℕ) : ℝ) * Real.log N -
        N * rateCluster p kmult (fun i => (n i : ℝ) / N) -
        ((N : ℝ) - (∑ i : Fin p, ((i : ℕ) + 1) * n i : ℕ)) ≤
      -(N * rateFunction p msf kmult (fun i => (n i : ℝ) / N)) + 1 + Real.log N := by
  set N' := ∑ i : Fin p, ((i : ℕ) + 1) * n i with hN'
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hP : (0 : ℝ) < profileWeight n := by exact_mod_cast profileWeight_pos n
  have hlogP : Real.log (profileWeight n : ℝ) =
      ∑ i, ((n i : ℝ) * Real.log (((i : ℕ) + 1).factorial : ℝ) +
        Real.log ((n i).factorial : ℝ)) := by
    unfold profileWeight
    push_cast
    rw [Real.log_prod (fun i _ => by positivity)]
    refine sum_congr rfl fun i _ => ?_
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  rw [Real.log_div (by positivity) hP.ne', hlogP, rateFunction_eq]
  have hNsum : (N : ℝ) * ∑ i : Fin p, (n i : ℝ) / N * (Real.log ((i : ℕ) + 1).factorial - 1 +
      Real.log ((n i : ℝ) / N) - Real.log (msf ((i : ℕ) + 1))) =
      ∑ i : Fin p, ((n i : ℝ) * Real.log ((i : ℕ) + 1).factorial - n i +
        ((n i : ℝ) * Real.log (n i) - n i * Real.log N) - n i * Real.log (msf ((i : ℕ) + 1))) := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    have h := natCast_mul_log_div (ν := n i) hN
    have e : (N : ℝ) * ((n i : ℝ) / N * (Real.log ((i : ℕ) + 1).factorial - 1 +
        Real.log ((n i : ℝ) / N) - Real.log (msf ((i : ℕ) + 1)))) =
        (n i : ℝ) * Real.log ((i : ℕ) + 1).factorial - n i +
          (N : ℝ) * ((n i : ℝ) / N * Real.log ((n i : ℝ) / N)) -
          n i * Real.log (msf ((i : ℕ) + 1)) := by
      field_simp
    rw [e, h]
  -- the Stirling estimates
  have hst : ∀ i : Fin p, (n i : ℝ) * Real.log (n i) - n i ≤ Real.log ((n i).factorial : ℝ) :=
    fun i => log_factorial_ge' (n i)
  have hN'N := log_factorial_le_of_le hN hn
  have hmN' : (∑ i, n i : ℕ) ≤ N' := sum_le_sum fun i _ => Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have hcast : (((N' : ℕ) : ℝ) - ((∑ i, n i : ℕ) : ℝ)) = (((N' - ∑ i, n i : ℕ) : ℕ) : ℝ) := by
    rw [Nat.cast_sub hmN']
  rw [mul_add, mul_add, hNsum, mul_one]
  push_cast
  have hsum_st := sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin p))) => hst i
  simp only [sum_add_distrib, sum_sub_distrib] at hsum_st ⊢
  have hmlog : ∑ x : Fin p, (n x : ℝ) * Real.log N = (∑ x : Fin p, (n x : ℝ)) * Real.log N := by
    rw [sum_mul]
  rw [hmlog]
  linarith [hsum_st, hN'N]

end UpperBoundLDP

end MultipoleBKT

end
