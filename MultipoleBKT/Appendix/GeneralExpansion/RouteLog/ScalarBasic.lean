/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansion.RouteLog.CutMoments

/-!
# Scalar logarithmic normalization

See (A.42). Scalar powers are used only after logarithmic integration.
-/

@[expose] public section

namespace MultipoleBKT.GeneralExpansion

open MeasureTheory Set Metric
open scoped ENNReal

/-- A product of equal real powers with one distinguished factor. -/
theorem rpow_mul_pow_pred {x : ℝ} (hx : 0 < x) (a : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    x ^ a * (x ^ a) ^ (k - 1) = x ^ (a * k) := by
  rw [← pow_succ', Nat.sub_add_cancel hk, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]

/-- Uniform absorption only at the final scalar step. -/
theorem power_log_uniform {θ B : ℝ} (hθ : 0 < θ) (hB : 0 ≤ B) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      x ^ θ * (1 + B * |Real.log x|) ^ q ≤ C := by
  let t := θ / ((q : ℝ) + 1)
  have ht : 0 < t := div_pos hθ (by positivity)
  let C := (1 + B / t) ^ q
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun x hx hx1 => ?_⟩
  have hlog := (Real.abs_log_mul_self_rpow_lt x t hx hx1 ht).le
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.le _)] at hlog
  have hxp : x ^ t ≤ 1 := Real.rpow_le_one hx.le hx1 ht.le
  have hi : x ^ t * (1 + B * |Real.log x|) ≤ 1 + B / t := by
    have hb := mul_le_mul_of_nonneg_left hlog hB
    simp only [div_eq_mul_inv] at hb ⊢
    nlinarith
  have he : x ^ θ = x ^ t * (x ^ t) ^ q := by
    rw [← pow_succ', ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    dsimp only [t]
    push_cast
    field_simp
  rw [he]
  calc
    _ = x ^ t * (x ^ t * (1 + B * |Real.log x|)) ^ q := by rw [mul_pow]; ring
    _ ≤ 1 * (1 + B / t) ^ q :=
      mul_le_mul hxp (pow_le_pow_left₀ (by positivity) hi q) (by positivity) zero_le_one
    _ = C := one_mul _


end MultipoleBKT.GeneralExpansion

end
