/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansion.RouteLog.CutWeight
public import MultipoleBKT.Appendix.RouteLog.Radial
import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.Polar

/-!
# The logarithmic radial moments after root integration

See (A.42). Polar coordinates identify the
actual cut dipole integral with the scalar logarithmic moment.
-/

@[expose] public section

namespace MultipoleBKT.GeneralExpansion

open MeasureTheory Set Finset Metric
open scoped ENNReal
open MultipoleIntegral

variable {χ : ℂ → ℝ} {β lam h : ℝ}

/-- The scalar logarithmic moments are nonnegative on the stated parameter range. -/
theorem radialLogMoment_nonneg (a : ℝ) (q : ℕ) (hlam : 0 < lam) (hlh : lam ≤ h) :
    0 ≤ RouteLog.radialLogMoment a lam h q := by
  apply intervalIntegral.integral_nonneg (hlam.trans_le hlh).le
  intro t ht
  have hm : 0 < max t lam := lt_max_of_lt_right hlam
  have hlog := Real.log_nonneg ((one_le_div hm).2 (max_le ht.2 hlh))
  exact mul_nonneg (mul_nonneg ht.1 (Real.rpow_nonneg hm.le _)) (by positivity)

/-- Polar integration of the regularized logarithmic profile. -/
theorem lintegral_radial_log (hlam : 0 < lam) (hlh : lam ≤ h) (a : ℝ) (q : ℕ) :
    ∫⁻ w : ℂ, (closedBall (0 : ℂ) h).indicator
        (fun w => ENNReal.ofReal (max ‖w‖ lam ^ (a - 2) *
          (1 + Real.log (h / max ‖w‖ lam)) ^ q)) w =
      ENNReal.ofReal (2 * Real.pi * RouteLog.radialLogMoment a lam h q) := by
  let f (t : ℝ) := (Iic h).indicator
    (fun t => ENNReal.ofReal (max t lam ^ (a - 2) * (1 + Real.log (h / max t lam)) ^ q)) t
  have hf : Measurable f := by
    apply Measurable.indicator _ measurableSet_Iic
    fun_prop
  have he : (fun w : ℂ => (closedBall (0 : ℂ) h).indicator
      (fun w => ENNReal.ofReal (max ‖w‖ lam ^ (a - 2) *
        (1 + Real.log (h / max ‖w‖ lam)) ^ q)) w) = fun w => f ‖w‖ := by
    funext w
    simp only [f, Set.indicator, mem_closedBall_zero_iff, Set.mem_Iic]
  rw [he, lintegral_norm_eq f hf]
  have hp : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal t * f t =
      (Iic h).indicator (fun t => ENNReal.ofReal (t * max t lam ^ (a - 2) *
        (1 + Real.log (h / max t lam)) ^ q)) t := by
    intro t ht
    by_cases hth : t ≤ h
    · simp only [f, indicator_of_mem (show t ∈ Iic h from hth)]
      rw [← ENNReal.ofReal_mul ht.le]
      congr 1
      ring
    · simp [f, hth]
  rw [setLIntegral_congr_fun measurableSet_Ioi hp, setLIntegral_indicator measurableSet_Iic,
    Set.inter_comm, Ioi_inter_Iic, RouteLog.lintegral_radialLogMoment a q hlam hlh,
    ← ENNReal.ofReal_mul (by positivity)]

/-- The cut model weight with a logarithmic mark is bounded by the
literal polar logarithmic moment, before any regime estimate. -/
theorem lintegral_cutWeight_log_le (hχ : IsMollifier χ) (hβ : 0 ≤ β)
    (hlam : 0 < lam) (hlh : lam ≤ h) (q : ℕ) :
    ∫⁻ w, cutWeight χ β lam h w * ENNReal.ofReal
        (max ‖w‖ lam ^ 2 * (1 + Real.log (h / max ‖w‖ lam)) ^ q) ≤
      ENNReal.ofReal (2 * Real.pi * Real.exp (β * kernelConst χ) *
        RouteLog.radialLogMoment (4 - β) lam h q) := by
  have hp : ∀ w : ℂ, cutWeight χ β lam h w * ENNReal.ofReal
      (max ‖w‖ lam ^ 2 * (1 + Real.log (h / max ‖w‖ lam)) ^ q) ≤
      ENNReal.ofReal (Real.exp (β * kernelConst χ)) *
        (closedBall (0 : ℂ) h).indicator (fun w => ENNReal.ofReal
          (max ‖w‖ lam ^ ((4 - β) - 2) * (1 + Real.log (h / max ‖w‖ lam)) ^ q)) w := by
    intro w
    by_cases hw : w ∈ closedBall (0 : ℂ) h
    · unfold cutWeight
      rw [indicator_of_mem hw, indicator_of_mem hw]
      have hm : 0 < max ‖w‖ lam := lt_max_of_lt_right hlam
      have hl : 0 ≤ 1 + Real.log (h / max ‖w‖ lam) := by
        have := Real.log_nonneg ((one_le_div hm).2
          (max_le (mem_closedBall_zero_iff.mp hw) hlh))
        linarith
      calc
        _ ≤ ENNReal.ofReal (Real.exp (β * kernelConst χ) * max ‖w‖ lam ^ (-β)) *
            ENNReal.ofReal (max ‖w‖ lam ^ 2 * (1 + Real.log (h / max ‖w‖ lam)) ^ q) := by
          gcongr
          exact exp_smearedKernel_le hχ hβ hlam w
        _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show max ‖w‖ lam ^ ((4 - β) - 2) =
              max ‖w‖ lam ^ (-β) * max ‖w‖ lam ^ 2 by
            rw [← Real.rpow_two, ← Real.rpow_add hm]
            congr 1
            ring]
          ring
    · simp only [cutWeight, indicator_of_notMem hw, ENNReal.ofReal_zero, zero_mul, mul_zero]
      exact le_rfl
  refine (lintegral_mono hp).trans (le_of_eq ?_)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_radial_log hlam hlh,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end MultipoleBKT.GeneralExpansion

end
