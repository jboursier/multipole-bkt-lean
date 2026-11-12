/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansion.Radial

/-!
# Logarithmic spatial integrals

See the proof of Lemma A.4 and (A.41).
The annular inverse-square integral is kept as a logarithm. The truncated integral
splits into a disc and an annulus, as in the paper's common-translation estimate.
-/

@[expose] public section

namespace MultipoleBKT.RouteLog

open MeasureTheory Set
open scoped ENNReal

/-- The annular radial inverse-square integral, including its polar Jacobian.
This compatibility statement also allows reversed endpoints. Its integral is
`Appendix.integral_rpow_neg_one`, after cancelling the radial Jacobian. -/
theorem integral_annular_inverse_square {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ r in a..b, r / r ^ 2 = Real.log (b / a) := by
  have hkernel : (∫ r in a..b, r / r ^ 2) = ∫ r in a..b, r ^ (-1 : ℝ) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    have hr0 : 0 < r := (lt_min ha hb).trans_le hr.1
    rw [Real.rpow_neg_one]
    field_simp
  rw [hkernel]
  by_cases hab : a ≤ b
  · exact Appendix.integral_rpow_neg_one ha hab
  · rw [intervalIntegral.integral_symm,
      Appendix.integral_rpow_neg_one hb (le_of_not_ge hab),
      Real.log_div ha.ne' hb.ne', Real.log_div hb.ne' ha.ne']
    ring

/-- The lower Lebesgue integral of the radial annular kernel. -/
theorem lintegral_annular_inverse_square {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫⁻ r in Ioc a b, ENNReal.ofReal (r / r ^ 2) =
      ENNReal.ofReal (Real.log (b / a)) := by
  have hc : ContinuousOn (fun r : ℝ => r / r ^ 2) (Icc a b) := by
    refine continuousOn_id.div (continuousOn_id.pow 2) fun r hr => ?_
    exact pow_ne_zero _ (ha.trans_le hr.1).ne'
  rw [← ofReal_integral_eq_lintegral_ofReal
    (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun r hr =>
      div_nonneg (ha.trans hr.1).le (sq_nonneg _))),
    ← intervalIntegral.integral_of_le hab, integral_annular_inverse_square ha (ha.trans_le hab)]

/-- Polar coordinates give the logarithmic integral on a planar annulus. -/
theorem lintegral_planar_annular_inverse_square {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫⁻ z in {z : ℂ | ‖z‖ ∈ Ioc a b}, ENNReal.ofReal (‖z‖ ^ 2)⁻¹ =
      ENNReal.ofReal (2 * Real.pi * Real.log (b / a)) := by
  rw [TwoComponentCoulomb.lintegral_radial_set (Ioc a b) measurableSet_Ioc
    (fun r : ℝ => ENNReal.ofReal (r ^ 2)⁻¹) (by fun_prop)]
  have heq : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal r *
      ((Ioc a b).indicator (fun r => ENNReal.ofReal (r ^ 2)⁻¹) r *
        ENNReal.ofReal (2 * Real.pi)) =
      ENNReal.ofReal (2 * Real.pi) *
        (Ioc a b).indicator (fun r => ENNReal.ofReal (r / r ^ 2)) r := by
    intro r hr
    by_cases h : r ∈ Ioc a b
    · rw [indicator_of_mem h, indicator_of_mem h, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (r ^ 2)⁻¹),
        ← ENNReal.ofReal_mul hr.le, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    · simp only [indicator_of_notMem h, zero_mul, mul_zero]
  rw [setLIntegral_congr_fun measurableSet_Ioi heq,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,
    (show Ioc a b ∩ Ioi 0 = Ioc a b from inter_eq_left.2 (fun r hr => ha.trans hr.1)),
    lintegral_annular_inverse_square ha hab,
    ← ENNReal.ofReal_mul (by positivity)]

/-- The truncated radial inverse-square integral splits at its truncation radius. -/
theorem integral_truncated_inverse_square {R h : ℝ} (hR : 0 < R) (hRh : R ≤ h) :
    ∫ r in (0 : ℝ)..h, r / max r R ^ 2 = 1 / 2 + Real.log (h / R) := by
  have hc : Continuous (fun r : ℝ => r / max r R ^ 2) := by
    refine continuous_id.div ((continuous_id.max continuous_const).pow 2) fun r => ?_
    exact pow_ne_zero _ (lt_max_of_lt_right hR).ne'
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 R) (hc.intervalIntegrable R h)]
  have hlow : (∫ r in (0 : ℝ)..R, r / max r R ^ 2) = 1 / 2 := by
    calc
      _ = ∫ r in (0 : ℝ)..R, r / R ^ 2 :=
        intervalIntegral.integral_congr fun r hr => by
          rw [uIcc_of_le hR.le] at hr
          rw [max_eq_right hr.2]
      _ = 1 / 2 := by
        rw [intervalIntegral.integral_div, integral_id]
        field_simp
        ring
  have hhigh : (∫ r in R..h, r / max r R ^ 2) = Real.log (h / R) := by
    calc
      _ = ∫ r in R..h, r / r ^ 2 := intervalIntegral.integral_congr fun r hr => by
        rw [uIcc_of_le hRh] at hr
        rw [max_eq_left hr.1]
      _ = _ := integral_annular_inverse_square hR (hR.trans_le hRh)
  rw [hlow, hhigh]

/-- The common-translation integral in the plane, before estimating its logarithm. -/
theorem lintegral_planar_truncated_inverse_square {R h : ℝ} (hR : 0 < R) (hRh : R ≤ h) :
    ∫⁻ z in {z : ℂ | ‖z‖ ≤ h}, ENNReal.ofReal (max ‖z‖ R ^ 2)⁻¹ =
      ENNReal.ofReal (2 * Real.pi * (1 / 2 + Real.log (h / R))) := by
  have hh : 0 < h := hR.trans_le hRh
  have hc : Continuous (fun r : ℝ => r / max r R ^ 2) := by
    refine continuous_id.div ((continuous_id.max continuous_const).pow 2) fun r => ?_
    exact pow_ne_zero _ (lt_max_of_lt_right hR).ne'
  change (∫⁻ z in {z : ℂ | ‖z‖ ∈ Iic h}, _) = _
  rw [TwoComponentCoulomb.lintegral_radial_set (Iic h) measurableSet_Iic
    (fun r : ℝ => ENNReal.ofReal (max r R ^ 2)⁻¹) (by fun_prop)]
  have heq : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal r *
      ((Iic h).indicator (fun r => ENNReal.ofReal (max r R ^ 2)⁻¹) r *
        ENNReal.ofReal (2 * Real.pi)) =
      ENNReal.ofReal (2 * Real.pi) *
        (Ioc 0 h).indicator (fun r => ENNReal.ofReal (r / max r R ^ 2)) r := by
    intro r hr
    by_cases hrh : r ≤ h
    · rw [indicator_of_mem (show r ∈ Iic h from hrh),
        indicator_of_mem (show r ∈ Ioc 0 h from ⟨hr, hrh⟩),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ (max r R ^ 2)⁻¹),
        ← ENNReal.ofReal_mul hr.le, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    · rw [indicator_of_notMem (show r ∉ Iic h from hrh),
        indicator_of_notMem (show r ∉ Ioc 0 h from fun hx => hrh hx.2)]
      simp
  rw [setLIntegral_congr_fun measurableSet_Ioi heq,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.2 Ioc_subset_Ioi_self,
    ← ofReal_integral_eq_lintegral_ofReal
      (hc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun r hr =>
        div_nonneg hr.1.le (sq_nonneg _))),
    ← intervalIntegral.integral_of_le hh.le, integral_truncated_inverse_square hR hRh,
    ← ENNReal.ofReal_mul (by positivity)]

end MultipoleBKT.RouteLog

end
