/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.RouteLog.Radial
public import MultipoleBKT.Limits.Radial

/-!
# The radial split at the regularization scale

The proof of Lemma 4.58. The planar integral is
converted to the radial moment. Its split and negative-exponent bound
supply the core and annular denominators.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RouteFixedGroups

open MeasureTheory Set
open scoped ENNReal

/-- Polar coordinates identify the regularized planar moment with the radial moment. -/
theorem planar_max_moment {lam h : ℝ} (hlam : 0 < lam) (hlh : lam ≤ h) (E : ℝ) :
    (∫⁻ u : ℂ, (Metric.closedBall (0 : ℂ) h).indicator
      (fun u => ENNReal.ofReal (max ‖u‖ lam ^ E)) u) =
      ENNReal.ofReal (2 * Real.pi * RouteLog.radialLogMoment (E + 2) lam h 0) := by
  let f : ℝ → ℝ := (Iic h).indicator (fun r => max r lam ^ E)
  have hc : Continuous (fun r : ℝ => max r lam ^ E) :=
    (continuous_id.max continuous_const).rpow_const fun r => Or.inl (lt_max_of_lt_right hlam).ne'
  have hpt (u : ℂ) : (Metric.closedBall (0 : ℂ) h).indicator
      (fun u => ENNReal.ofReal (max ‖u‖ lam ^ E)) u = ENNReal.ofReal (f ‖u‖) := by
    by_cases hu : ‖u‖ ≤ h
    · rw [indicator_of_mem (show u ∈ Metric.closedBall (0 : ℂ) h by simpa using hu)]
      change _ = ENNReal.ofReal ((Iic h).indicator _ ‖u‖)
      rw [indicator_of_mem (show ‖u‖ ∈ Iic h from hu)]
    · rw [indicator_of_notMem (show u ∉ Metric.closedBall (0 : ℂ) h by simpa using hu)]
      change _ = ENNReal.ofReal ((Iic h).indicator _ ‖u‖)
      rw [indicator_of_notMem (show ‖u‖ ∉ Iic h from hu), ENNReal.ofReal_zero]
  have hint : Integrable fun u : ℂ => f ‖u‖ := by
    have hi : IntegrableOn (fun u : ℂ => max ‖u‖ lam ^ E) (Metric.closedBall (0 : ℂ) h) :=
      (hc.comp continuous_norm).continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) h)
    refine ((integrable_indicator_iff measurableSet_closedBall).mpr hi).congr ?_
    apply Filter.Eventually.of_forall
    intro u
    by_cases hu : ‖u‖ ≤ h
    · rw [indicator_of_mem (show u ∈ Metric.closedBall (0 : ℂ) h by simpa using hu)]
      exact (indicator_of_mem (show ‖u‖ ∈ Iic h from hu) (fun r : ℝ => max r lam ^ E)).symm
    · rw [indicator_of_notMem (show u ∉ Metric.closedBall (0 : ℂ) h by simpa using hu)]
      exact (indicator_of_notMem (show ‖u‖ ∉ Iic h from hu) (fun r : ℝ => max r lam ^ E)).symm
  have hf0 (u : ℂ) : 0 ≤ f ‖u‖ := indicator_nonneg
    (fun r _ => Real.rpow_nonneg (le_max_of_le_right hlam.le) E) _
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hf0),
    integral_fun_norm_complex f]
  congr 1
  congr 1
  rw [RouteLog.radialLogMoment]
  simp only [add_sub_cancel_right, pow_zero, mul_one]
  have heq : ∀ r ∈ Ioi (0 : ℝ), f r * r =
      (Ioc 0 h).indicator (fun r => r * max r lam ^ E) r := by
    intro r hr
    by_cases hrh : r ≤ h
    · rw [show f r = max r lam ^ E from indicator_of_mem (show r ∈ Iic h from hrh) _, indicator_of_mem (show r ∈ Ioc (0 : ℝ) h from ⟨hr, hrh⟩)]
      ring
    · rw [show f r = 0 from indicator_of_notMem (show r ∉ Iic h from hrh) _, indicator_of_notMem (fun ht => hrh ht.2), zero_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, Ioc_inter_Ioi, max_self,
    ← intervalIntegral.integral_of_le (hlam.trans_le hlh).le]

/-- The negative radial regime, using the radial tail estimate. -/
theorem planar_max_moment_le_of_neg {lam h E : ℝ} (hlam : 0 < lam) (hlh : lam ≤ h)
    (hE : E + 2 < 0) :
    (∫⁻ u : ℂ, (Metric.closedBall (0 : ℂ) h).indicator
      (fun u => ENNReal.ofReal (max ‖u‖ lam ^ E)) u) ≤
      ENNReal.ofReal (2 * Real.pi * ((1 / 2 + 1 / (-(E + 2))) * lam ^ (E + 2))) := by
  rw [planar_max_moment hlam hlh E]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [pow_zero, mul_one] using RouteLog.radialLogMoment_le_of_neg hE 0 hlam hlh

/-- The positive radial regime, from the split at `λ`. -/
theorem planar_max_moment_le_of_pos {lam h E : ℝ} (hlam : 0 < lam) (hlh : lam ≤ h)
    (hE : 0 < E + 2) :
    (∫⁻ u : ℂ, (Metric.closedBall (0 : ℂ) h).indicator
      (fun u => ENNReal.ofReal (max ‖u‖ lam ^ E)) u) ≤
      ENNReal.ofReal (2 * Real.pi * ((1 + 1 / (E + 2)) * h ^ (E + 2))) := by
  rw [planar_max_moment hlam hlh E]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [RouteLog.radialLogMoment_split (E + 2) 0 hlam hlh]
  simp only [pow_zero, mul_one]
  rw [integral_rpow (Or.inr ⟨by linarith, by
    rw [uIcc_of_le hlh]
    exact fun ht => (not_le_of_gt hlam) ht.1⟩)]
  rw [show E + 2 - 1 + 1 = E + 2 by ring]
  have hl : lam ^ (E + 2) ≤ h ^ (E + 2) := Real.rpow_le_rpow hlam.le hlh hE.le
  have hp : 0 ≤ lam ^ (E + 2) := Real.rpow_nonneg hlam.le _
  have hhp : 0 ≤ h ^ (E + 2) := Real.rpow_nonneg (hlam.trans_le hlh).le _
  have hd : 0 ≤ 1 / (E + 2) := by positivity
  simp only [div_eq_mul_inv] at *
  nlinarith

/-- The one-radius calculation printed for `β ≥ 4`.
The radial integral supplies the annulus after the split at `λ`. -/
theorem high_beta_radius_split_majorant {lam h a E : ℝ} (hlam : 0 < lam) (hlh : lam ≤ h)
    (_ha2 : a < 2) (hE : E - a + 2 < 0) :
    h ^ a * ((lam ^ E * (lam ^ (2 - a) / (2 - a))) +
      (RouteLog.radialLogMoment (E - a + 2) lam h 0 - lam ^ (E - a + 2) / 2)) ≤
      h ^ a * lam ^ (E - a + 2) * (1 / (2 - a) + 1 / (-(E - a + 2))) := by
  have hb := RouteLog.radialLogMoment_le_of_neg hE 0 hlam hlh
  simp only [pow_zero, mul_one] at hb
  have hp : lam ^ E * lam ^ (2 - a) = lam ^ (E - a + 2) := by
    rw [← Real.rpow_add hlam]
    congr 1
    ring
  have hleft : lam ^ E * (lam ^ (2 - a) / (2 - a)) = lam ^ (E - a + 2) / (2 - a) := by
    rw [← mul_div_assoc, hp]
  rw [hleft]
  have hh : 0 ≤ h ^ a := Real.rpow_nonneg (hlam.trans_le hlh).le _
  calc
    _ ≤ h ^ a * (lam ^ (E - a + 2) / (2 - a) +
        ((1 / 2 + 1 / (-(E - a + 2))) * lam ^ (E - a + 2) - lam ^ (E - a + 2) / 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl (sub_le_sub_right hb _)) hh
    _ = _ := by ring

/-- The literal one-radius integral printed before (A.69).
The core has exponent `1-a`, and the annulus is the zeroth radial moment. -/
theorem high_beta_radius_split {lam h a E : ℝ} (hlam : 0 < lam) (hlh : lam ≤ h)
    (ha2 : a < 2) (hE : E - a + 2 < 0) :
    h ^ a * (∫ r in (0 : ℝ)..h, r ^ (1 - a) * max r lam ^ E) ≤
      h ^ a * lam ^ (E - a + 2) * (1 / (2 - a) + 1 / (-(E - a + 2))) := by
  let f : ℝ → ℝ := fun r => r ^ (1 - a) * max r lam ^ E
  have hcore_eq : EqOn f (fun r => lam ^ E * r ^ (1 - a)) (uIcc 0 lam) := by
    intro r hr
    rw [uIcc_of_le hlam.le] at hr
    dsimp only [f]
    rw [max_eq_right hr.2, mul_comm]
  have htail_eq : EqOn f (fun r => r ^ (E - a + 1)) (uIcc lam h) := by
    intro r hr
    rw [uIcc_of_le hlh] at hr
    dsimp only [f]
    rw [max_eq_left hr.1, ← Real.rpow_add (hlam.trans_le hr.1)]
    congr 1
    ring
  have hcore : IntervalIntegrable f volume 0 lam :=
    (intervalIntegrable_congr (hcore_eq.mono uIoc_subset_uIcc)).mpr
      ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < 1 - a)).const_mul (lam ^ E))
  have htail : IntervalIntegrable f volume lam h :=
    (intervalIntegrable_congr (htail_eq.mono uIoc_subset_uIcc)).mpr
      (intervalIntegral.intervalIntegrable_rpow (Or.inr (by
        rw [uIcc_of_le hlh]
        exact fun hr => (not_le_of_gt hlam) hr.1)))
  have hcoreI : (∫ r in (0 : ℝ)..lam, f r) = lam ^ E * (lam ^ (2 - a) / (2 - a)) := by
    rw [intervalIntegral.integral_congr hcore_eq, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith))]
    rw [show 1 - a + 1 = 2 - a by ring, Real.zero_rpow (by linarith), sub_zero]
  have htailI : (∫ r in lam..h, f r) =
      RouteLog.radialLogMoment (E - a + 2) lam h 0 - lam ^ (E - a + 2) / 2 := by
    rw [intervalIntegral.integral_congr htail_eq]
    have he := RouteLog.radialLogMoment_split (E - a + 2) 0 hlam hlh
    simp only [pow_zero, mul_one] at he
    rw [show E - a + 2 - 1 = E - a + 1 by ring] at he
    linarith
  have heq : (∫ r in (0 : ℝ)..h, f r) = lam ^ E * (lam ^ (2 - a) / (2 - a)) +
      (RouteLog.radialLogMoment (E - a + 2) lam h 0 - lam ^ (E - a + 2) / 2) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hcore htail, hcoreI, htailI]
  change h ^ a * (∫ r in (0 : ℝ)..h, f r) ≤ _
  rw [heq]
  exact high_beta_radius_split_majorant hlam hlh ha2 hE

end MultipoleBKT.AbsoluteLower.RouteFixedGroups

end
