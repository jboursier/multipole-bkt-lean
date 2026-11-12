/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.DipoleConstant
public import MultipoleBKT.Appendix.RadialIntegral

/-!
# Radial integrals with a cutoff

The integrals of Sections 5.12–5.14 are integrals over discs of powers of `max(|u|, λ)`. In polar
coordinates (`integral_fun_norm_complex`),
`∫_{|u| ≤ h} max(|u|, λ)^E du ≤ 2π ∫₀^h max(r, λ)^{E+1} dr`
(`lintegral_closedBall_max_rpow_le`), and the right-hand side is evaluated by Lemma A.2's
radial computations (`Appendix.radial_bounds_pos`, `Appendix.radial_bounds_neg`,
`Appendix.radial_value_zero`):

* `E + 2 > 0`: `≤ 2π (1 + 1/(E+2)) h^{E+2}` (`lintegral_closedBall_max_rpow_le_of_pos`);
* `E + 2 < 0`: `≤ 2π (1 + 1/|E+2|) λ^{E+2}` (`lintegral_closedBall_max_rpow_le_of_neg`);
* `E + 2 = 0`: `= 2π (1 + log(h/λ))` (`lintegral_closedBall_max_rpow_le_of_eq`).
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open MeasureTheory Set
open scoped ENNReal

variable {lam h E : ℝ}

/-- **Polar coordinates with a cutoff**:
`∫_{|u| ≤ h} max(|u|, λ)^E du ≤ 2π ∫₀^∞ 𝟙_{r ≤ h} max(r, λ)^{E+1} dr`. -/
theorem lintegral_closedBall_max_rpow_le (hlam : 0 < lam) (h E : ℝ) :
    ∫⁻ u : ℂ, (Metric.closedBall (0 : ℂ) h).indicator
        (fun u => ENNReal.ofReal (max ‖u‖ lam ^ E)) u ≤
      ENNReal.ofReal (2 * Real.pi *
        ∫ r in Ioi (0 : ℝ), (Iic h).indicator (fun r => max r lam ^ (E + 2 - 1)) r) := by
  have hcont : ∀ e : ℝ, Continuous fun r : ℝ => max r lam ^ e := fun e =>
    Appendix.continuous_max_rpow hlam e
  set f : ℝ → ℝ := (Iic h).indicator (fun r => max r lam ^ E) with hf
  have hpt : ∀ u : ℂ, (Metric.closedBall (0 : ℂ) h).indicator
      (fun u => ENNReal.ofReal (max ‖u‖ lam ^ E)) u = ENNReal.ofReal (f ‖u‖) := by
    intro u
    by_cases hu : u ∈ Metric.closedBall (0 : ℂ) h
    · have hu' : ‖u‖ ∈ Iic h := by
        rw [Metric.mem_closedBall, dist_zero_right] at hu
        exact hu
      rw [Set.indicator_of_mem hu, hf, Set.indicator_of_mem hu']
    · have hu' : ‖u‖ ∉ Iic h := by
        rw [Metric.mem_closedBall, dist_zero_right] at hu
        exact hu
      rw [Set.indicator_of_notMem hu, hf, Set.indicator_of_notMem hu', ENNReal.ofReal_zero]
  have hf0 : ∀ t, 0 ≤ f t := fun t => by
    simp only [hf]
    exact Set.indicator_nonneg (fun r _ => Real.rpow_nonneg
      (le_max_of_le_right hlam.le) _) t
  -- integrability of the radial integrand on the plane
  have hint : Integrable fun u : ℂ => f ‖u‖ := by
    have hset : IntegrableOn (fun u : ℂ => max ‖u‖ lam ^ E) (Metric.closedBall (0 : ℂ) h) :=
      ((hcont E).comp continuous_norm).continuousOn.integrableOn_compact
        (isCompact_closedBall _ _)
    refine ((integrable_indicator_iff measurableSet_closedBall).2 hset).congr
      (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    by_cases hu : u ∈ Metric.closedBall (0 : ℂ) h
    · have hu' : ‖u‖ ∈ Iic h := by
        rw [Metric.mem_closedBall, dist_zero_right] at hu
        exact hu
      rw [Set.indicator_of_mem hu, hf, Set.indicator_of_mem hu']
    · have hu' : ‖u‖ ∉ Iic h := by
        rw [Metric.mem_closedBall, dist_zero_right] at hu
        exact hu
      rw [Set.indicator_of_notMem hu, hf, Set.indicator_of_notMem hu']
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun u => hf0 _),
    integral_fun_norm_complex f]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
  -- the comparison `f r r ≤ 𝟙_{r ≤ h} max(r, λ)^{E+1}` on `(0, ∞)`
  have hg : IntegrableOn (fun r => (Iic h).indicator (fun r => max r lam ^ (E + 2 - 1)) r)
      (Ioi 0) := by
    unfold IntegrableOn
    rw [integrable_indicator_iff measurableSet_Iic]
    unfold IntegrableOn
    rw [Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioi]
    exact ((hcont _).continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hfr : IntegrableOn (fun r => f r * r) (Ioi 0) :=
    (integrable_fun_norm_complex_iff f).1 hint
  refine setIntegral_mono_on hfr hg measurableSet_Ioi fun r hr => ?_
  by_cases hrh : r ∈ Iic h
  · simp only [hf, Set.indicator_of_mem hrh]
    have hm : 0 < max r lam := lt_max_of_lt_right hlam
    rw [show E + 2 - 1 = E + 1 by ring, Real.rpow_add_one hm.ne']
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.rpow_nonneg hm.le _)
  · simp only [hf, Set.indicator_of_notMem hrh, zero_mul, le_refl]

/-- `E + 2 > 0`: `∫_{|u| ≤ h} max(|u|, λ)^E ≤ 2π (1 + 1/(E+2)) h^{E+2}` for `λ ≤ h`. -/
theorem lintegral_closedBall_max_rpow_le_of_pos (hlam : 0 < lam) (hlh : lam ≤ h)
    (hE : 0 < E + 2) :
    ∫⁻ u : ℂ, (Metric.closedBall (0 : ℂ) h).indicator
        (fun u => ENNReal.ofReal (max ‖u‖ lam ^ E)) u ≤
      ENNReal.ofReal (2 * Real.pi * ((1 + 1 / (E + 2)) * h ^ (E + 2))) := by
  refine (lintegral_closedBall_max_rpow_le hlam h E).trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_left (Appendix.radial_bounds_pos hlam hlh hE).2 (by positivity)

/-- `E + 2 < 0`: `∫_{|u| ≤ h} max(|u|, λ)^E ≤ 2π (1 + 1/|E+2|) λ^{E+2}` for `λ ≤ h`. -/
theorem lintegral_closedBall_max_rpow_le_of_neg (hlam : 0 < lam) (hlh : lam ≤ h)
    (hE : E + 2 < 0) :
    ∫⁻ u : ℂ, (Metric.closedBall (0 : ℂ) h).indicator
        (fun u => ENNReal.ofReal (max ‖u‖ lam ^ E)) u ≤
      ENNReal.ofReal (2 * Real.pi * ((1 + 1 / (-(E + 2))) * lam ^ (E + 2))) := by
  refine (lintegral_closedBall_max_rpow_le hlam h E).trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_left (Appendix.radial_bounds_neg hlam hlh hE).2 (by positivity)

/-- `E = -2`: `∫_{|u| ≤ h} max(|u|, λ)^{-2} ≤ 2π (1 + log(h/λ))` for `λ ≤ h`. -/
theorem lintegral_closedBall_max_rpow_le_of_eq (hlam : 0 < lam) (hlh : lam ≤ h) :
    ∫⁻ u : ℂ, (Metric.closedBall (0 : ℂ) h).indicator
        (fun u => ENNReal.ofReal (max ‖u‖ lam ^ (-2 : ℝ))) u ≤
      ENNReal.ofReal (2 * Real.pi * (1 + Real.log (h / lam))) := by
  refine (lintegral_closedBall_max_rpow_le hlam h (-2)).trans (le_of_eq ?_)
  congr 2
  rw [show (-2 : ℝ) + 2 - 1 = 0 - 1 by ring]
  exact Appendix.radial_value_zero hlam hlh

end BadPointTypes

end MultipoleBKT

end
