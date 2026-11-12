/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.RouteProfiles.Sums

/-!
# Inserting the ambient profile constraint

(4.22) in
proof of Lemma 4.59. Half the cutoff
power pays for the ambient profile, leaving a geometric gain in the
total label size. The prescribed block is never charged to the ambient
profile and retains its own inverse power of lambda.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RouteProfiles

/-- The cutoff pays for the ambient profile for every block size `s ≥ 1`. -/
theorem cutoff_weight_le {ε α A lam N n : ℝ} {s : ℕ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hα : 0 ≤ α) (hA : 0 ≤ A)
    (hlam : 0 < lam) (hN : 0 < N) (hs : 1 ≤ s)
    (hn : n ≤ N * ε ^ (-α) * lam ^ (2 * (s - 1))) :
    n * ((A * ε ^ (2 * α)) ^ s / (lam ^ (2 * (s - 1)) * N)) ≤
      (A * ε ^ α) ^ s := by
  have hcut : ε ^ (-α) * (ε ^ (2 * α)) ^ s ≤ (ε ^ α) ^ s := by
    rw [← Real.rpow_mul_natCast hε.le, ← Real.rpow_mul_natCast hε.le, ← Real.rpow_add hε]
    apply Real.rpow_le_rpow_of_exponent_ge hε hε1
    have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
    nlinarith
  calc _ ≤ (N * ε ^ (-α) * lam ^ (2 * (s - 1))) *
        ((A * ε ^ (2 * α)) ^ s / (lam ^ (2 * (s - 1)) * N)) := by
          exact mul_le_mul_of_nonneg_right hn (by positivity)
    _ = A ^ s * (ε ^ (-α) * (ε ^ (2 * α)) ^ s) := by rw [mul_pow]; field_simp
    _ ≤ A ^ s * (ε ^ α) ^ s := mul_le_mul_of_nonneg_left hcut (pow_nonneg hA _)
    _ = _ := (mul_pow _ _ _).symm

/-- Cancel `N` in the prescribed block's weight, retaining its exact size. -/
theorem prescribed_weight {N lam t D : ℝ} (hN : N ≠ 0) {r : ℕ} :
    D * N * (t ^ r / (lam ^ (2 * (r - 1)) * N)) =
      D * t ^ r / lam ^ (2 * (r - 1)) := by
  by_cases hl : lam ^ (2 * (r - 1)) = 0
  · simp [hl]
  · field_simp

end MultipoleBKT.AbsoluteLower.RouteProfiles

end
