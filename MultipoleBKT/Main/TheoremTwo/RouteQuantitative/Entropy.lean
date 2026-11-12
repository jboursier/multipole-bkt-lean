/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.TheoremTwo.RateAnalysis

/-!
# Quantitative entropy rounding

Direct entropy comparisons in Steps 1 and 3 of the proof of Theorem 2.
The logarithmic modulus includes the boundary coordinate zero.
-/

@[expose] public section

namespace MultipoleBKT.TheoremTwo

open Finset Set

/-- The small-coordinate part of the entropy comparison at mesh `1/N`. -/
theorem abs_mul_log_le_mesh {N : ℕ} (hN : 1 ≤ N) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (1 / N)) :
    |x * Real.log x| ≤ (Real.log N + 1) / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hx1 : x ≤ 1 := hx.2.trans (by rw [div_le_one hN0]; exact hN1)
  rw [abs_of_nonpos (Real.mul_log_nonpos hx.1 hx1)]
  rcases hx.1.eq_or_lt with heq | hx0
  · rw [← heq, zero_mul, neg_zero]
    positivity
  · have h := Real.self_sub_one_le_mul_log (by positivity : 0 ≤ (N : ℝ) * x)
    rw [Real.log_mul hN0.ne' hx0.ne'] at h
    have hxN : (N : ℝ) * x ≤ 1 := by nlinarith [(le_div_iff₀ hN0).mp hx.2]
    have hprod := mul_le_mul_of_nonneg_right hxN hlog
    rw [le_div_iff₀ hN0]
    nlinarith

/-- The ordered large-coordinate comparison uses `log(a/b) ≤ a/b-1`. -/
theorem abs_mul_log_sub_le_mesh_ordered {N : ℕ} (hN : 1 ≤ N) {D a b : ℝ}
    (hD : 1 ≤ D) (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) a)
    (hab : a - b ≤ D / N) :
    |a * Real.log a - b * Real.log b| ≤ 2 * D * (Real.log N + 1) / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  by_cases ham : a ≤ 1 / N
  · have h1 := abs_mul_log_le_mesh hN ⟨ha.1, ham⟩
    have h2 := abs_mul_log_le_mesh hN ⟨hb.1, hb.2.trans ham⟩
    calc |a * Real.log a - b * Real.log b| ≤ |a * Real.log a| + |b * Real.log b| := abs_sub _ _
      _ ≤ (Real.log N + 1) / N + (Real.log N + 1) / N := add_le_add h1 h2
      _ ≤ 2 * D * (Real.log N + 1) / N := by
        rw [← add_div, div_le_div_iff_of_pos_right hN0]
        nlinarith
  · have ha0 : 0 < a := (by positivity : (0 : ℝ) < 1 / N).trans (lt_of_not_ge ham)
    have hla : -Real.log N ≤ Real.log a := by
      rw [← Real.log_inv, ← one_div]
      exact Real.log_le_log (by positivity) (le_of_not_ge ham)
    have hdiff : 0 ≤ a - b := sub_nonneg.mpr hb.2
    have hupper : a * Real.log a - b * Real.log b ≤ a - b := by
      have ht := entropy_sub_le_tangent (A := 0) hb.1 ha0
      simp only [zero_add] at ht
      have := mul_nonpos_of_nonpos_of_nonneg (Real.log_nonpos ha.1 ha.2) hdiff
      nlinarith
    have hlower : -(a - b) * Real.log N ≤ a * Real.log a - b * Real.log b := by
      have hmono : b * Real.log b ≤ b * Real.log a := by
        rcases hb.1.eq_or_lt with heq | hb0
        · rw [← heq, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (Real.log_le_log hb0 hb.2) hb.1
      have := mul_le_mul_of_nonneg_left hla hdiff
      nlinarith
    rw [abs_le]
    have hdN := (le_div_iff₀ hN0).mp hab
    have h1 := mul_le_mul_of_nonneg_right hdN hlog
    constructor
    · rw [neg_le, le_div_iff₀ hN0]
      nlinarith [mul_le_mul_of_nonneg_right hlower hN0.le]
    · rw [le_div_iff₀ hN0]
      nlinarith [mul_le_mul_of_nonneg_right hupper hN0.le]

/-- A uniform boundary-inclusive entropy error for coordinates within `D/N`. -/
theorem abs_mul_log_sub_le_mesh {N : ℕ} (hN : 1 ≤ N) {D a b : ℝ}
    (hD : 1 ≤ D) (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hab : |a - b| ≤ D / N) :
    |a * Real.log a - b * Real.log b| ≤ 2 * D * (Real.log N + 1) / N := by
  rcases le_total b a with h | h
  · exact abs_mul_log_sub_le_mesh_ordered hN hD ha ⟨hb.1, h⟩ ((le_abs_self _).trans hab)
  · rw [abs_sub_comm]
    exact abs_mul_log_sub_le_mesh_ordered hN hD hb ⟨ha.1, h⟩
      ((le_abs_self _).trans (by rwa [abs_sub_comm] at hab))

end MultipoleBKT.TheoremTwo

end
