/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeTwoCount.HomogeneousBound

/-!
# Normalization of the homogeneous count

The paper: Lemma 5.42.
Insert one integrated `2k`-pole per block into the factorial count and collect
its powers of the ambient volume and the cutoff scale.
-/

@[expose] public section

namespace MultipoleBKT.BadPointTypes.RouteTypeTwoCount

/-- The factorial count with the integrated contribution of each `2k`-pole. -/
theorem homogeneous_multipole_bound {U Nr lam β : ℝ} {n k q : ℕ}
    (hU : 0 < U) (hN : 0 < Nr) (hlam : 0 < lam) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hsize : k * q = n) :
    (n.factorial : ℝ) / (k.factorial ^ q * q.factorial) *
        (U * Nr * lam ^ ((4 - β) * k - 2)) ^ q ≤
      (Real.exp 1 * max 1 U * n * lam ^ (2 - β)) ^ n *
        (Nr * lam ^ (2 * (k - 1)) / n) ^ ((n : ℝ) / k) := by
  set B := U * Nr * lam ^ ((4 - β) * k - 2) with hB
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hq : (n : ℝ) / k = q := by
    rw [div_eq_iff hk0.ne']
    exact_mod_cast (by rw [← hsize, Nat.mul_comm] : n = q * k)
  -- the power of `B / n`
  have hBn : (B / n) ^ ((n : ℝ) / k) ≤
      max 1 U ^ n * (lam ^ (2 - β)) ^ n * (Nr * lam ^ (2 * (k - 1)) / n) ^ ((n : ℝ) / k) := by
    have hsplit : lam ^ ((4 - β) * k - 2) =
        lam ^ ((4 - β) * k - 2 - 2 * (k - 1 : ℝ)) * lam ^ (2 * (k - 1)) := by
      rw [← Real.rpow_natCast lam (2 * (k - 1)), ← Real.rpow_add hlam]
      congr 1
      push_cast [Nat.cast_sub hk]
      ring
    have e1 : B / n = U * lam ^ ((4 - β) * k - 2 - 2 * (k - 1 : ℝ)) *
        (Nr * lam ^ (2 * (k - 1)) / n) := by
      rw [hB, hsplit]
      field_simp
    rw [e1, Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hU.le (by positivity)]
    have e2 : (lam ^ ((4 - β) * k - 2 - 2 * (k - 1 : ℝ))) ^ ((n : ℝ) / k) = (lam ^ (2 - β)) ^ n := by
      rw [← Real.rpow_mul hlam.le, ← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
      congr 1
      field_simp
      ring
    rw [e2]
    have e3 : U ^ ((n : ℝ) / k) ≤ max 1 U ^ n := by
      calc U ^ ((n : ℝ) / k) ≤ (max 1 U) ^ ((n : ℝ) / k) :=
            Real.rpow_le_rpow hU.le (le_max_right _ _) (by positivity)
        _ ≤ (max 1 U) ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le (le_max_left _ _)
            (div_le_self hn0.le (by exact_mod_cast hk))
        _ = max 1 U ^ n := Real.rpow_natCast _ _
    have hpos : 0 ≤ (lam ^ (2 - β)) ^ n * (Nr * lam ^ (2 * (k - 1)) / n) ^ ((n : ℝ) / k) := by
      positivity
    calc U ^ ((n : ℝ) / k) * (lam ^ (2 - β)) ^ n * (Nr * lam ^ (2 * (k - 1)) / n) ^ ((n : ℝ) / k)
        = U ^ ((n : ℝ) / k) * ((lam ^ (2 - β)) ^ n *
            (Nr * lam ^ (2 * (k - 1)) / n) ^ ((n : ℝ) / k)) := by ring
      _ ≤ max 1 U ^ n * ((lam ^ (2 - β)) ^ n *
            (Nr * lam ^ (2 * (k - 1)) / n) ^ ((n : ℝ) / k)) :=
          mul_le_mul_of_nonneg_right e3 hpos
      _ = _ := by ring
  have hc := homogeneous_factorial_bound hn hk hsize (B := B) (by positivity)
  rw [← Real.rpow_natCast (B / n) q, ← hq] at hc
  calc (n.factorial : ℝ) / (k.factorial ^ q * q.factorial) * B ^ q
      ≤ (n : ℝ) ^ n * (B / n) ^ ((n : ℝ) / k) * Real.exp 1 ^ n := hc
    _ ≤ (n : ℝ) ^ n * (max 1 U ^ n * (lam ^ (2 - β)) ^ n *
        (Nr * lam ^ (2 * (k - 1)) / n) ^ ((n : ℝ) / k)) * Real.exp 1 ^ n := by
          gcongr
    _ = _ := by rw [mul_pow, mul_pow, mul_pow]; ring

end MultipoleBKT.BadPointTypes.RouteTypeTwoCount

end
