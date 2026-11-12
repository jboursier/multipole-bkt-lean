/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansion.RouteLog.ScalarBasic

/-!
# Compatibility bounds after the zeroth logarithmic moment

See (A.42). Evaluate the moment in the
three regimes first. The consumed root and tail interfaces retain a
positive exponent, which is introduced only in the final scalar comparison.
-/

@[expose] public section

namespace MultipoleBKT.GeneralExpansion

open MeasureTheory Set Metric
open scoped ENNReal
open MultipoleIntegral

/-- Final comparison of a logarithm with a positive power of its argument. -/
theorem log_growth_le {t σ : ℝ} (ht : 1 ≤ t) (hσ : 0 < σ) :
    1 + Real.log t ≤ (1 + 1 / σ) * t ^ σ := by
  have hp := Real.one_le_rpow ht hσ.le
  have hl := Real.log_le_rpow_div (zero_le_one.trans ht) hσ
  simp only [div_eq_mul_inv] at hl ⊢
  nlinarith

/-- The zeroth moment is compared with the compatibility power only after
its subcritical, critical or supercritical evaluation. -/
theorem radial_moment_zero_power {β σ : ℝ} (hβ : 2 < β) (hσ : 0 < σ)
    (hσβ : 4 - β ≤ σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      RouteLog.radialLogMoment (4 - β) lam h 0 ≤ C * lam ^ (4 - β - σ) * h ^ σ := by
  by_cases hlt : β < 4
  · let a := 4 - β
    have ha : 0 < a := by dsimp only [a]; linarith
    have ha2 : a ≤ 2 := by dsimp only [a]; linarith
    refine ⟨RouteLog.momentConstant a 0, RouteLog.momentConstant_pos ha 0,
      fun lam h hlam hlh => ?_⟩
    have hh : 0 < h := hlam.trans_le hlh
    have hp : h ^ a ≤ lam ^ (a - σ) * h ^ σ := by
      have he : h ^ a = h ^ (a - σ) * h ^ σ := by rw [← Real.rpow_add hh]; congr 1; ring
      rw [he]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hlam hlh (by linarith))
        (Real.rpow_nonneg hh.le _)
    calc
      _ ≤ RouteLog.momentConstant a 0 * h ^ a := RouteLog.radialLogMoment_le_of_pos ha ha2 0 hlam hlh
      _ ≤ RouteLog.momentConstant a 0 * (lam ^ (a - σ) * h ^ σ) :=
        mul_le_mul_of_nonneg_left hp (RouteLog.momentConstant_pos ha 0).le
      _ = _ := by ring
  · by_cases heq : β = 4
    · subst β
      refine ⟨(3 / 2 : ℝ) * (1 + 1 / σ), by positivity, fun lam h hlam hlh => ?_⟩
      have h0 : RouteLog.radialLogMoment 0 lam h 0 ≤ 3 / 2 * (1 + Real.log (h / lam)) := by
        convert RouteLog.radialLogMoment_le_zero 0 hlam hlh using 1
        norm_num
      have hg := log_growth_le ((one_le_div hlam).2 hlh) hσ
      have he : (h / lam) ^ σ = lam ^ (-σ) * h ^ σ := by
        rw [Real.div_rpow (hlam.trans_le hlh).le hlam.le, Real.rpow_neg hlam.le]
        ring
      simp only [sub_self, zero_sub]
      calc
        _ ≤ 3 / 2 * (1 + Real.log (h / lam)) := h0
        _ ≤ 3 / 2 * ((1 + 1 / σ) * (h / lam) ^ σ) := by gcongr
        _ = _ := by rw [he]; ring
    · have hgt : 4 < β := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
      let a := 4 - β
      have ha : a < 0 := by dsimp only [a]; linarith
      let C := 1 / 2 + 1 / (-a)
      have hC : 0 < C := by
        have : 0 < -a := neg_pos.mpr ha
        dsimp only [C]
        positivity
      refine ⟨C, hC, fun lam h hlam hlh => ?_⟩
      have hp : lam ^ a ≤ lam ^ (a - σ) * h ^ σ := by
        rw [show lam ^ a = lam ^ (a - σ) * lam ^ σ by
          rw [← Real.rpow_add hlam]; congr 1; ring]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hlam.le hlh hσ.le)
          (Real.rpow_nonneg hlam.le _)
      calc
        _ ≤ C * lam ^ a := by
          simpa only [pow_zero, mul_one] using RouteLog.radialLogMoment_le_of_neg ha 0 hlam hlh
        _ ≤ C * (lam ^ (a - σ) * h ^ σ) := by gcongr
        _ = _ := by ring

/-- The actual smeared square-weighted integral, after its logarithmic
moment has been evaluated in the appropriate regime. -/
theorem cut_square_power {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β σ : ℝ}
    (hβ : 2 < β) (hσ : 0 < σ) (hσβ : 4 - β ≤ σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      (∫⁻ w, cutWeight χ β lam h w * ENNReal.ofReal (max ‖w‖ lam ^ 2)) ≤
        ENNReal.ofReal (C * lam ^ (4 - β - σ) * h ^ σ) := by
  obtain ⟨C, hC, hbound⟩ := radial_moment_zero_power hβ hσ hσβ
  let K := 2 * Real.pi * Real.exp (β * kernelConst χ)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K * C, mul_pos hK hC, fun lam h hlam hlh => ?_⟩
  have hh := lintegral_cutWeight_log_le (β := β) hχ (by linarith) hlam hlh 0
  simp only [pow_zero, mul_one] at hh
  refine hh.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ K * (C * lam ^ (4 - β - σ) * h ^ σ) := mul_le_mul_of_nonneg_left
      (hbound lam h hlam hlh) hK.le
    _ = _ := by ring

/-- Internal square-weighted comparison after the scalar moment integration. -/
theorem internal_cut_square_mul_power {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β σ : ℝ}
    (hβ : 2 < β) (hσ : 0 < σ) (hσβ : 4 - β ≤ σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      ∀ a : ℝ, 0 ≤ a → ∀ g : ℂ → ℝ≥0∞,
        (∀ w, g w ≤ ENNReal.ofReal (a * max ‖w‖ lam ^ 2)) →
        (∫⁻ w, cutWeight χ β lam h w * g w) ≤
          ENNReal.ofReal (a * C * (lam ^ (4 - β - σ) * h ^ σ)) := by
  obtain ⟨C, hC, hbound⟩ := cut_square_power hχ hβ hσ hσβ
  refine ⟨C, hC, fun lam h hlam hlh a ha g hg => ?_⟩
  calc
    _ ≤ ∫⁻ w, ENNReal.ofReal a * (cutWeight χ β lam h w *
        ENNReal.ofReal (max ‖w‖ lam ^ 2)) := lintegral_mono fun w => by
      calc
        _ ≤ cutWeight χ β lam h w * ENNReal.ofReal (a * max ‖w‖ lam ^ 2) :=
          mul_le_mul' le_rfl (hg w)
        _ = _ := by rw [ENNReal.ofReal_mul ha]; ring
    _ = ENNReal.ofReal a * ∫⁻ w, cutWeight χ β lam h w *
        ENNReal.ofReal (max ‖w‖ lam ^ 2) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal a * ENNReal.ofReal (C * lam ^ (4 - β - σ) * h ^ σ) :=
      mul_le_mul' le_rfl (hbound lam h hlam hlh)
    _ = _ := by rw [← ENNReal.ofReal_mul ha]; congr 1; ring

end MultipoleBKT.GeneralExpansion

end
