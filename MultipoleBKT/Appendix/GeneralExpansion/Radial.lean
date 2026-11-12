/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.Basic
public import MultipoleBKT.Appendix.RadialIntegral
public import TwoComponentCoulomb.LowerBound.PolarPi

/-!
# Planar radial integration and compatibility estimates

See Lemma A.6. These elementary planar formulas also serve consumers. The multipole-error proof uses the logarithmic formulas in
`RouteLog/RootGeometry`, `RouteLog/CutMoments` and `RouteLog/TailMoments`.
The remaining positive-exponent helpers are consumed by the small-integral
and cluster-error interfaces.
-/

@[expose] public section

namespace MultipoleBKT

namespace GeneralExpansion

open MeasureTheory Set
open scoped ENNReal
open MultipoleIntegral

variable {lam : ℝ}

/-- `t · max(t, λ)^e ≤ max(t, λ)^{e+1}` for `0 ≤ t`, `λ > 0`. -/
theorem mul_max_rpow_le (hlam : 0 < lam) (t e : ℝ) :
    t * max t lam ^ e ≤ max t lam ^ (e + 1) := by
  have hm : 0 < max t lam := lt_max_of_lt_right hlam
  rw [Real.rpow_add_one hm.ne', mul_comm]
  exact mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.rpow_nonneg hm.le _)

/-- **The ball integral.** For `e > -2`, `λ > 0` and `ρ ≥ 0`,
`∫_{|w| ≤ ρ} max(|w|, λ)^e dw ≤ 2π (1 + 1/(e+2)) max(ρ, λ)^{e+2}`. -/
theorem lintegral_ball_max_rpow_le (hlam : 0 < lam) {e : ℝ} (he : -2 < e) (ρ : ℝ) :
    ∫⁻ u in {u : ℂ | ‖u‖ ∈ Iic ρ}, ENNReal.ofReal (max ‖u‖ lam ^ e) ≤
      ENNReal.ofReal (2 * Real.pi * (1 + 1 / (e + 2)) * max ρ lam ^ (e + 2)) := by
  set ρ' := max ρ lam
  have hlρ : lam ≤ ρ' := le_max_right _ _
  have hmeas : Measurable fun t : ℝ => ENNReal.ofReal (max t lam ^ e) :=
    ENNReal.measurable_ofReal.comp (Appendix.continuous_max_rpow hlam e).measurable
  rw [TwoComponentCoulomb.lintegral_radial_set (Iic ρ) measurableSet_Iic _ hmeas]
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal t *
      ((Iic ρ).indicator (fun t => ENNReal.ofReal (max t lam ^ e)) t *
        ENNReal.ofReal (2 * Real.pi)) ≤
      ENNReal.ofReal ((Iic ρ').indicator (fun r => 2 * Real.pi * max r lam ^ ((e + 2) - 1)) t) := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    by_cases htρ : t ∈ Iic ρ
    · have htρ' : t ∈ Iic ρ' := (show t ≤ ρ' from (show t ≤ ρ from htρ).trans (le_max_left _ _))
      rw [indicator_of_mem htρ, indicator_of_mem htρ', ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul ht0]
      refine ENNReal.ofReal_le_ofReal ?_
      have := mul_max_rpow_le hlam t e
      rw [show e + 2 - 1 = e + 1 by ring]
      nlinarith [Real.pi_pos]
    · rw [indicator_of_notMem htρ, zero_mul, mul_zero]
      exact zero_le
  refine (setLIntegral_mono' measurableSet_Ioi hpt).trans ?_
  have hint : Integrable ((Iic ρ').indicator (fun r => 2 * Real.pi * max r lam ^ ((e + 2) - 1)))
      (volume.restrict (Ioi 0)) := by
    have := (Appendix.integrable_radialIndicator hlam ρ' ((e + 2) - 1)).const_mul (2 * Real.pi)
    refine this.congr (Filter.Eventually.of_forall fun r => ?_)
    simp only [indicator_apply]
    split_ifs <;> simp
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun r =>
    indicator_nonneg (fun r _ => by positivity) r)]
  refine ENNReal.ofReal_le_ofReal ?_
  have heq : ∫ r in Ioi (0 : ℝ), (Iic ρ').indicator
      (fun r => 2 * Real.pi * max r lam ^ ((e + 2) - 1)) r =
      2 * Real.pi * ∫ r in Ioi (0 : ℝ), (Iic ρ').indicator (fun r => max r lam ^ ((e + 2) - 1)) r := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only [indicator_apply]
    split_ifs <;> simp
  rw [heq]
  have hb := (Appendix.radial_bounds_pos hlam hlρ (show 0 < e + 2 by linarith)).2
  have := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  linarith

/-- **The tail integral.** For `e < -2` and `0 < λ ≤ ρ`,
`∫_{|w| > ρ} max(|w|, λ)^e dw ≤ 2π ρ^{e+2} / (-(e+2))`. -/
theorem lintegral_tail_max_rpow_le (hlam : 0 < lam) {e : ℝ} (he : e < -2) {ρ : ℝ}
    (hlρ : lam ≤ ρ) :
    ∫⁻ u in {u : ℂ | ‖u‖ ∈ Ioi ρ}, ENNReal.ofReal (max ‖u‖ lam ^ e) ≤
      ENNReal.ofReal (2 * Real.pi * (ρ ^ (e + 2) / (-(e + 2)))) := by
  have hρ : 0 < ρ := hlam.trans_le hlρ
  have hmeas : Measurable fun t : ℝ => ENNReal.ofReal (max t lam ^ e) :=
    ENNReal.measurable_ofReal.comp (Appendix.continuous_max_rpow hlam e).measurable
  rw [TwoComponentCoulomb.lintegral_radial_set (Ioi ρ) measurableSet_Ioi _ hmeas]
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal t *
      ((Ioi ρ).indicator (fun t => ENNReal.ofReal (max t lam ^ e)) t *
        ENNReal.ofReal (2 * Real.pi)) =
      (Ioi ρ).indicator (fun t => ENNReal.ofReal (2 * Real.pi * t ^ (e + 1))) t := by
    intro t ht
    by_cases htρ : t ∈ Ioi ρ
    · have htl : lam ≤ t := hlρ.trans (le_of_lt htρ)
      have ht0 : 0 < t := hρ.trans htρ
      rw [indicator_of_mem htρ, indicator_of_mem htρ, max_eq_left htl,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul ht0.le]
      congr 1
      rw [Real.rpow_add_one ht0.ne']
      ring
    · rw [indicator_of_notMem htρ, indicator_of_notMem htρ, zero_mul, mul_zero]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Set.inter_eq_left.2 (Ioi_subset_Ioi hρ.le)]
  have hint : IntegrableOn (fun t : ℝ => 2 * Real.pi * t ^ (e + 1)) (Ioi ρ) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hρ).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht =>
      by have : 0 < t := hρ.trans ht; positivity))]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hρ]
  rw [show e + 1 + 1 = e + 2 by ring, neg_div, div_neg]


/-- **The singular ball integral.** For `0 < η` and `ρ > 0`,
`∫_{|y - q| < ρ} |y - q|^{η-2} dy ≤ 2π ρ^η / η`. -/
theorem lintegral_ball_sing_le {η : ℝ} (hη : 0 < η) {ρ : ℝ} (hρ : 0 < ρ) (q : ℂ) :
    ∫⁻ y : ℂ, (Metric.ball q ρ).indicator (fun y => ENNReal.ofReal (‖y - q‖ ^ (η - 2))) y ≤
      ENNReal.ofReal (2 * Real.pi * (ρ ^ η / η)) := by
  have hshift : ∫⁻ y : ℂ, (Metric.ball q ρ).indicator
      (fun y => ENNReal.ofReal (‖y - q‖ ^ (η - 2))) y =
      ∫⁻ y : ℂ, (Metric.ball (0 : ℂ) ρ).indicator (fun y => ENNReal.ofReal (‖y‖ ^ (η - 2))) y := by
    rw [← lintegral_sub_right_eq_self (fun y : ℂ => (Metric.ball (0 : ℂ) ρ).indicator
      (fun y => ENNReal.ofReal (‖y‖ ^ (η - 2))) y) q]
    congr 1
    funext y
    have hmem : y ∈ Metric.ball q ρ ↔ y - q ∈ Metric.ball (0 : ℂ) ρ := by
      simp [Metric.mem_ball, dist_eq_norm]
    by_cases hy : y ∈ Metric.ball q ρ
    · rw [indicator_of_mem hy, indicator_of_mem (hmem.1 hy)]
    · rw [indicator_of_notMem hy, indicator_of_notMem (fun h => hy (hmem.2 h))]
  rw [hshift]
  have hset : Metric.ball (0 : ℂ) ρ = {u : ℂ | ‖u‖ ∈ Iio ρ} := by
    ext u
    simp [Metric.mem_ball, dist_eq_norm]
  rw [hset, lintegral_indicator (by rw [← hset]; exact Metric.isOpen_ball.measurableSet)]
  have hmeas : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (η - 2)) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [TwoComponentCoulomb.lintegral_radial_set (Iio ρ) measurableSet_Iio _ hmeas]
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal t *
      ((Iio ρ).indicator (fun t => ENNReal.ofReal (t ^ (η - 2))) t *
        ENNReal.ofReal (2 * Real.pi)) =
      (Ioo 0 ρ).indicator (fun t => ENNReal.ofReal (2 * Real.pi * t ^ (η - 1))) t := by
    intro t ht
    have ht0 : 0 < t := ht
    by_cases htρ : t ∈ Iio ρ
    · have hmem : t ∈ Ioo 0 ρ := ⟨ht0, htρ⟩
      rw [indicator_of_mem htρ, indicator_of_mem hmem, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul ht0.le]
      congr 1
      have : t ^ (η - 1) = t * t ^ (η - 2) := by
        rw [show η - 1 = (η - 2) + 1 by ring, Real.rpow_add_one ht0.ne']
        ring
      rw [this]
      ring
    · have hmem : t ∉ Ioo 0 ρ := fun h => htρ h.2
      rw [indicator_of_notMem htρ, indicator_of_notMem hmem, zero_mul, mul_zero]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo,
    Set.inter_eq_left.2 Set.Ioo_subset_Ioi_self]
  have hint : IntegrableOn (fun t : ℝ => 2 * Real.pi * t ^ (η - 1)) (Ioo 0 ρ) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := ρ)
      (r := η - 1) (by linarith)).const_mul (2 * Real.pi)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hρ.le] at this
    exact this.mono_set Ioo_subset_Ioc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun t ht =>
      by have : 0 < t := ht.1; positivity))]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hρ.le,
    integral_rpow (Or.inl (by linarith))]
  rw [show η - 1 + 1 = η by ring, Real.zero_rpow hη.ne', sub_zero]

/-- **The inner radial integral of Step 3** (in the proof of Lemma A.6):
for `σ > 0` with `4 - β ≤ σ`, `λ > 0` and `ρ ≥ 0`,
`∫_{|s| ≤ ρ} max(|s|, λ)^{2-β} ds ≤ 2π (1 + 1/σ) λ^{4-β-σ} max(ρ, λ)^σ`. -/
theorem lintegral_ball_max_rpow_two_sub_le (hlam : 0 < lam) {β σ : ℝ} (hσ : 0 < σ)
    (hσβ : 4 - β ≤ σ) (ρ : ℝ) :
    ∫⁻ u in {u : ℂ | ‖u‖ ∈ Iic ρ}, ENNReal.ofReal (max ‖u‖ lam ^ (2 - β)) ≤
      ENNReal.ofReal (lam ^ (4 - β - σ) * (2 * Real.pi * (1 + 1 / σ) * max ρ lam ^ σ)) := by
  have hpt : ∀ u : ℂ, ENNReal.ofReal (max ‖u‖ lam ^ (2 - β)) ≤
      ENNReal.ofReal (lam ^ (4 - β - σ)) * ENNReal.ofReal (max ‖u‖ lam ^ (σ - 2)) := by
    intro u
    have hm : 0 < max ‖u‖ lam := lt_max_of_lt_right hlam
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hlam.le _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : max ‖u‖ lam ^ (2 - β) = max ‖u‖ lam ^ (4 - β - σ) * max ‖u‖ lam ^ (σ - 2) := by
      rw [← Real.rpow_add hm]
      ring_nf
    rw [h1]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hlam (le_max_right _ _) (by linarith))
      (Real.rpow_nonneg hm.le _)
  calc ∫⁻ u in {u : ℂ | ‖u‖ ∈ Iic ρ}, ENNReal.ofReal (max ‖u‖ lam ^ (2 - β))
      ≤ ∫⁻ u in {u : ℂ | ‖u‖ ∈ Iic ρ},
          ENNReal.ofReal (lam ^ (4 - β - σ)) * ENNReal.ofReal (max ‖u‖ lam ^ (σ - 2)) :=
        lintegral_mono fun u => hpt u
    _ = ENNReal.ofReal (lam ^ (4 - β - σ)) *
          ∫⁻ u in {u : ℂ | ‖u‖ ∈ Iic ρ}, ENNReal.ofReal (max ‖u‖ lam ^ (σ - 2)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (lam ^ (4 - β - σ)) *
          ENNReal.ofReal (2 * Real.pi * (1 + 1 / (σ - 2 + 2)) * max ρ lam ^ (σ - 2 + 2)) := by
        gcongr
        exact lintegral_ball_max_rpow_le hlam (by linarith) ρ
    _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hlam.le _)]
        congr 2
        ring_nf


end GeneralExpansion

end MultipoleBKT

end
