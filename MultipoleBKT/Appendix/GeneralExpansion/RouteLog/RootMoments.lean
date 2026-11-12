/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansion.RouteLog.RootGeometry
public import MultipoleBKT.Appendix.GeneralExpansion.RouteLog.ScalarGain

/-!
# Integrating the root logarithm against the actual dipole weight

See (A.43) and
(A.44). The cap, bad-root area and inverse-square
logarithm are kept as separate terms until the radial moments are integrated.
-/

@[expose] public section

namespace MultipoleBKT.GeneralExpansion

open MeasureTheory Set Finset Metric
open scoped ENNReal
open MultipoleIntegral UpperBound MultipoleIntegralZ

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ : ℝ}
  {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}

/-- Root integration followed by the literal logarithmic radial moments.
The coefficient of the bad-point term is independent of the cutoff. -/
theorem lintegral_rootZ_moments_le (hχ : IsMollifier χ) (hβ : 0 ≤ β)
    (hlam : 0 < lam) (hlh : lam ≤ ε₀ * truncationScale p₀ β lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) (hV : badPointsOn p₀ β lam M ε₀ V Z = V) :
    ∫⁻ w, cutWeight χ β lam (ε₀ * truncationScale p₀ β lam) w *
        ∫⁻ y, rootZ p₀ β lam M ε₀ V Z w y ≤
      ENNReal.ofReal (2 * Real.pi * Real.exp (β * MultipoleIntegral.kernelConst χ) *
        ((N / (ε₀ * truncationScale p₀ β lam) ^ 2 + 4 * V.card * Real.pi * M ^ 2) *
            RouteLog.radialLogMoment (4 - β) lam (ε₀ * truncationScale p₀ β lam) 0 +
          (128 * Real.pi * (1 + Real.log 17) * V.card) *
            RouteLog.radialLogMoment (4 - β) lam (ε₀ * truncationScale p₀ β lam) 1)) := by
  let h := ε₀ * truncationScale p₀ β lam
  let a := (N : ℝ) / h ^ 2 + 4 * V.card * Real.pi * M ^ 2
  let b := 128 * Real.pi * (1 + Real.log 17) * V.card
  have hh : 0 < h := hlam.trans_le hlh
  have h4 : 0 ≤ Real.log 17 := Real.log_nonneg (by norm_num)
  have h417 : Real.log 4 ≤ Real.log 17 := Real.log_le_log (by norm_num) (by norm_num)
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  let G (q : ℕ) (w : ℂ) := ENNReal.ofReal
    (max ‖w‖ lam ^ 2 * (1 + Real.log (h / max ‖w‖ lam)) ^ q)
  have hpt : ∀ w, cutWeight χ β lam h w * ∫⁻ y, rootZ p₀ β lam M ε₀ V Z w y ≤
      ENNReal.ofReal a * (cutWeight χ β lam h w * G 0 w) +
        ENNReal.ofReal b * (cutWeight χ β lam h w * G 1 w) := by
    intro w
    by_cases hw : ‖w‖ ≤ h
    · have hm : 0 < max ‖w‖ lam := lt_max_of_lt_right hlam
      have hmh : max ‖w‖ lam ≤ h := max_le hw hlh
      have hl : 0 ≤ Real.log (h / max ‖w‖ lam) := Real.log_nonneg ((one_le_div hm).2 hmh)
      have he : Real.log (4 * h / max ‖w‖ lam) = Real.log 4 + Real.log (h / max ‖w‖ lam) := by
        rw [mul_div_assoc, Real.log_mul (by norm_num) (div_pos hh hm).ne']
      have he17 : Real.log (17 * h / max ‖w‖ lam) =
          Real.log 17 + Real.log (h / max ‖w‖ lam) := by
        rw [mul_div_assoc, Real.log_mul (by norm_num) (div_pos hh hm).ne']
      have hmark : 1 / 2 + Real.log (4 * h / max ‖w‖ lam) ≤
          1 + Real.log (17 * h / max ‖w‖ lam) := by rw [he, he17]; linarith
      have hbnd : 1 / 2 + Real.log (4 * h / max ‖w‖ lam) ≤
          (1 + Real.log 17) * (1 + Real.log (h / max ‖w‖ lam)) := by
        refine hmark.trans ?_
        rw [he17]
        nlinarith [mul_nonneg h4 hl]
      have hroot := lintegral_rootZ_log_le hlam hlh hM hV hw
      calc
        _ ≤ cutWeight χ β lam h w * ENNReal.ofReal
            (N * (max ‖w‖ lam ^ 2 / h ^ 2) +
              4 * V.card * (16 * max ‖w‖ lam ^ 2 *
                (2 * Real.pi * (1 / 2 + Real.log (4 * h / max ‖w‖ lam))) +
                  Real.pi * (M * max ‖w‖ lam) ^ 2)) := mul_le_mul' le_rfl hroot
        _ ≤ cutWeight χ β lam h w *
            (ENNReal.ofReal a * G 0 w + ENNReal.ofReal b * G 1 w) := by
          apply mul_le_mul' le_rfl
          dsimp only [G]
          rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hb,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          simp only [pow_zero, pow_one, mul_one, a, b]
          have hb' := mul_le_mul_of_nonneg_left hbnd
            (show 0 ≤ 128 * Real.pi * (V.card : ℝ) * max ‖w‖ lam ^ 2 by positivity)
          simp only [div_eq_mul_inv] at hb' ⊢
          nlinarith
        _ = _ := by ring
    · have hz : cutWeight χ β lam h w = 0 := by
        simp only [cutWeight, indicator_of_notMem (show w ∉ closedBall (0 : ℂ) h from
          fun hx => hw (mem_closedBall_zero_iff.mp hx)), ENNReal.ofReal_zero]
      simp only [hz, zero_mul, mul_zero, add_zero, le_refl]
  have hG : Measurable fun w => ENNReal.ofReal a * (cutWeight χ β lam h w * G 0 w) := by
    refine Measurable.mul measurable_const ((measurable_cutWeight hχ hlam β h).mul ?_)
    dsimp only [G]
    fun_prop
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_add_left hG, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    _ ≤ ENNReal.ofReal a * ENNReal.ofReal (2 * Real.pi * Real.exp (β * MultipoleIntegral.kernelConst χ) *
          RouteLog.radialLogMoment (4 - β) lam h 0) +
        ENNReal.ofReal b * ENNReal.ofReal (2 * Real.pi * Real.exp (β * MultipoleIntegral.kernelConst χ) *
          RouteLog.radialLogMoment (4 - β) lam h 1) := by
      gcongr
      · exact lintegral_cutWeight_log_le hχ hβ hlam hlh 0
      · exact lintegral_cutWeight_log_le hχ hβ hlam hlh 1
    _ = _ := by
      have h0 := radialLogMoment_nonneg (4 - β) 0 hlam hlh
      have h1 := radialLogMoment_nonneg (4 - β) 1 hlam hlh
      rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hb,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end MultipoleBKT.GeneralExpansion

end
