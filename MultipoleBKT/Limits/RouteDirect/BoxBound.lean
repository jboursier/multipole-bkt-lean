/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteDirect.Anchor
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# The root factor in the dipole integral bound

See Lemma A.5 of the paper. The common translation costs at most the area `N`.
-/

@[expose] public section

namespace MultipoleBKT.Limits.RouteDirect

open MeasureTheory Filter
open scoped ENNReal

variable {I : Type*} [Fintype I] [Nonempty I]

/-- Integration of the common translation contributes at most `N`. -/
theorem integral_boxConfig_abs_le_anchor (root : I) {F : (I → ℂ × ℂ) → ℝ}
    (hF : Measurable F) (hinv : TranslationInvariant F)
    (hint : Integrable fun c => anchorR root c * F c) (N : ℕ) :
    (∫ c in boxConfig I N, |F c|) ≤ (N : ℝ) * ∫ c, |anchorR root c * F c| := by
  have heq (c : I → ℂ × ℂ) : |anchorR root c * F c| = anchorR root c * |F c| := by
    rw [abs_mul, abs_of_nonneg (anchorR_nonneg root c)]
  have hinta : Integrable fun c => anchorR root c * |F c| := by
    simpa only [heq] using hint.abs
  have hFa : Measurable (fun c => |F c|) := by simpa only [Real.norm_eq_abs] using hF.norm
  rw [(integral_boxConfig_eq N root hFa (fun a c => by rw [hinv a c]) hinta).2]
  calc
    _ ≤ ∫ c, (N : ℝ) * (anchorR root c * |F c|) := by
      apply integral_mono_of_nonneg
      · exact Eventually.of_forall fun c => mul_nonneg
          (mul_nonneg (anchorR_nonneg root c) (abs_nonneg _)) ENNReal.toReal_nonneg
      · exact hinta.const_mul N
      · exact Eventually.of_forall fun c => by
          have ho : (overlap N c).toReal ≤ N :=
            ENNReal.toReal_le_of_le_ofReal (Nat.cast_nonneg N) (by simpa using overlap_le N c)
          exact (mul_le_mul_of_nonneg_left ho
            (mul_nonneg (anchorR_nonneg root c) (abs_nonneg _))).trans_eq (by ring)
    _ = _ := by rw [integral_const_mul]; simp_rw [heq]

omit [Nonempty I] in
/-- The real rooted absolute integral is bounded by a finite nonnegative
upper bound for its nonnegative integral. -/
theorem integral_anchor_abs_le (root : I) {F : (I → ℂ × ℂ) → ℝ}
    (hint : Integrable fun c => anchorR root c * F c) {a : ℝ} (ha : 0 ≤ a)
    (hle : (∫⁻ c, anchor root c * ENNReal.ofReal |F c|) ≤ ENNReal.ofReal a) :
    (∫ c, |anchorR root c * F c|) ≤ a := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun c => abs_nonneg _)
    hint.abs.aestronglyMeasurable]
  have heq (c : I → ℂ × ℂ) : ENNReal.ofReal |anchorR root c * F c| =
      anchor root c * ENNReal.ofReal |F c| := by
    rw [abs_mul, abs_of_nonneg (anchorR_nonneg root c),
      ENNReal.ofReal_mul (anchorR_nonneg root c), ofReal_anchorR]
  simp_rw [heq]
  exact ENNReal.toReal_le_of_le_ofReal ha hle

end MultipoleBKT.Limits.RouteDirect

end
