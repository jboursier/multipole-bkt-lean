/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.UpperBoundLDP.Entropy
public import MultipoleBKT.UpperBound.UpperBoundLDP.RouteNormalization.Log

/-!
# Final entropy calculation after logarithmic normalization

The paper: Proposition 5.43,
Step 3. Write `N log C` as the full-plane logarithm
plus its error, using the upper half of the two-sided (4.11) estimate.
Retain `K N R̄⁻²` through the logarithmic bookkeeping, then use `R̄⁻² ≤ δ`
and absorb `1 + log N` in `N δ`.
-/

@[expose] public section

open Finset

namespace MultipoleBKT.UpperBoundLDP.RouteNormalization

open PropFiveFortyFive

/-- Internal entropy calculation with a quantitative logarithmic normalization
(the paper, Proposition 5.43). -/
theorem upper_entropy_bound_of_log_normalization {p N : ℕ} (hN : 1 ≤ N) (n : Fin p → ℕ)
    (hn : ∑ i : Fin p, ((i : ℕ) + 1) * n i ≤ N) (msf : ℕ → ℝ) (kmult : (ℕ →₀ ℕ) → ℝ)
    {Cn K R lam β Z t t' L₀ Cbb C₃₈ Kδ KV δ : ℝ} (hCn : 0 < Cn)
    (hnorm : N * Real.log Cn -
      (N * (2 - β) * Real.log lam + N * Real.log Z) ≤ K * N * R)
    (hK : 0 ≤ K) (hRδ : R ≤ δ)
    (ht' : t' = t + β * L₀ + β * Cbb + KV + 1) (hlogN : 1 + Real.log N ≤ δ * N) :
    (N.factorial : ℝ) * ((N : ℝ) * Cn) ^ N *
        (((∑ i : Fin p, ((i : ℕ) + 1) * n i).factorial : ℝ) / profileWeight n) *
        Real.exp ((∑ i, (n i : ℝ) * Real.log (msf ((i : ℕ) + 1)) -
            ((∑ i : Fin p, ((i : ℕ) + 1) * n i : ℕ) - (∑ i, n i : ℕ) : ℝ) * Real.log N -
            N * rateCluster p kmult (fun i => (n i : ℝ) / N) + Kδ * N * δ +
            KV * (N - ∑ i : Fin p, ((i : ℕ) + 1) * n i : ℕ)) +
          (t + β * L₀ + β * Cbb - t') * (N - ∑ i : Fin p, ((i : ℕ) + 1) * n i : ℕ) +
          C₃₈ * N * δ) ≤
      Real.exp (N * Real.log N + Real.log (N.factorial : ℝ) + N * (2 - β) * Real.log lam +
        N * Real.log Z - N * rateFunction p msf kmult (fun i => (n i : ℝ) / N) +
        (C₃₈ + Kδ + K + 1) * N * δ) := by
  set N' := ∑ i : Fin p, ((i : ℕ) + 1) * n i with hN'
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hF : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hq : (0 : ℝ) < (N'.factorial : ℝ) / profileWeight n := by
    have := profileWeight_pos n
    have := Nat.factorial_pos N'
    positivity
  have hV : (((N - N' : ℕ) : ℕ) : ℝ) = (N : ℝ) - N' := by rw [Nat.cast_sub hn]
  have hent := log_profile_le hN n hn msf kmult
  rw [← hN'] at hent
  -- Keep the normalization correction before absorbing the final errors.
  have hnormalization : (N : ℝ) * Real.log ((N : ℝ) * Cn) =
      N * Real.log N + N * (2 - β) * Real.log lam + N * Real.log Z +
        (N * Real.log Cn - (N * (2 - β) * Real.log lam + N * Real.log Z)) := by
    rw [Real.log_mul hN0.ne' hCn.ne']
    ring
  have hpos : 0 < (N.factorial : ℝ) * ((N : ℝ) * Cn) ^ N *
      ((N'.factorial : ℝ) / profileWeight n) := by positivity
  rw [← Real.exp_log hpos, ← Real.exp_add, Real.exp_le_exp,
    Real.log_mul (by positivity) hq.ne', Real.log_mul hF.ne' (by positivity), Real.log_pow]
  rw [hV] at *
  rw [ht', hnormalization]
  have habsorb : K * (N : ℝ) * R ≤ K * N * δ :=
    mul_le_mul_of_nonneg_left hRδ (mul_nonneg hK hN0.le)
  nlinarith [hent, hnorm, habsorb, hlogN]

end MultipoleBKT.UpperBoundLDP.RouteNormalization

end
