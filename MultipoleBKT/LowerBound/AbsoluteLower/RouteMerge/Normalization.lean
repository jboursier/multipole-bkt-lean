/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.ENNReal.Real

/-!
# Normalization arithmetic for the lower simplification

The proof of Lemma 4.57. This internal scalar lemma
absorbs the marking multiplicity, dipole normalization, and block comparison.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RouteMerge

/-- The normalization coefficient after the two tree levels have merged.
The hypotheses are scalar inputs to this internal arithmetic lemma. -/
theorem coefficient_le {k q : ℕ} {N lam β Cnorm Mm Z0 C₁ K W c Z C : ℝ}
    (hq : q ≤ k) (hN : 0 < N) (hlam : 0 < lam) (hCn : 0 < Cnorm)
    (hMm : 0 ≤ Mm) (hZ0 : 0 ≤ Z0) (hC₁ : 0 ≤ C₁) (hK : 0 ≤ K)
    (hW : 0 ≤ W) (hZ : 0 < Z)
    (hcomp : Z0 ≤ Real.exp (c * k) * Mm)
    (hratio : lam ^ (2 - β) / Cnorm ≤ 2 / Z)
    (hbase : Real.exp c * C₁ * W * K * 2 * (2 / Z) ≤ Real.exp C) :
    ENNReal.ofReal (C₁ ^ k * ((N * Cnorm)⁻¹ ^ k * Mm⁻¹ * W ^ k) * K ^ k * (2 : ℝ) ^ q) ≤
      ENNReal.ofReal (Real.exp (C * k)) / ENNReal.ofReal ((N * lam ^ (2 - β)) ^ k * Z0) := by
  apply (ENNReal.le_div_iff_mul_le
    (Or.inr (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))))
    (Or.inl ENNReal.ofReal_ne_top)).mpr
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rcases hMm.eq_or_lt with hz | hm
  · rw [← hz, inv_zero]
    simp only [mul_zero, zero_mul]
    exact (Real.exp_pos _).le
  have h2 : (2 : ℝ) ^ q ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hq
  calc
    _ ≤ (C₁ ^ k * ((N * Cnorm)⁻¹ ^ k * Mm⁻¹ * W ^ k) * K ^ k * (2 : ℝ) ^ k) *
        ((N * lam ^ (2 - β)) ^ k * (Real.exp (c * k) * Mm)) := by gcongr
    _ = (Real.exp c * C₁ * W * K * 2) ^ k * (lam ^ (2 - β) / Cnorm) ^ k := by
      rw [show Real.exp (c * k) = Real.exp c ^ k by rw [← Real.exp_nat_mul, mul_comm]]
      simp only [mul_pow, div_pow, inv_pow]
      field_simp
    _ ≤ (Real.exp c * C₁ * W * K * 2) ^ k * (2 / Z) ^ k := by gcongr
    _ ≤ Real.exp C ^ k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hbase k
    _ = Real.exp (C * k) := by rw [← Real.exp_nat_mul, mul_comm]

end MultipoleBKT.AbsoluteLower.RouteMerge

end
