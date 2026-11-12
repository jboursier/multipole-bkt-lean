/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.SmearedCharge
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import TwoComponentCoulomb.Potential.DiscField

/-!
# Radial mass profiles for bounded measurable charges

See Lemmas 3.1 and 3.2 of the paper. The radial mass is absolutely continuous on
each bounded interval of nonnegative radii. Its almost everywhere derivative is
the polar density, even when the mollifier is only bounded and measurable.

This module is below both `Potential.Regularity` and `Potential.Electric`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace MultipoleBKT

variable {χ : ℂ → ℝ} {lam : ℝ}

/-- Domination by Lebesgue measure: `δ_z^{(λ)}(S) ≤ (M / λ²) |S|` for `S` of finite volume. -/
theorem smearedCharge_real_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M) (hlam : 0 < lam)
    (z : ℂ) {S : Set ℂ} (hS : volume S ≠ ∞) :
    (smearedCharge χ z lam).real S ≤ M / lam ^ 2 * volume.real S := by
  have hM0 : 0 ≤ M := hχ.nonneg_of_le hM
  have h1 : smearedCharge χ z lam S ≤ ENNReal.ofReal (M / lam ^ 2) * volume S := by
    refine (smearedCharge_le_smul_restrict hχ hM hlam S).trans ?_
    rw [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_right (Measure.restrict_apply_le _ _) _
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS) h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h2
  simpa only [measureReal_def] using h2

/-- The area of a disc: `|B(a, r)| = π r²` for `r ≥ 0`. -/
theorem volume_real_ball_complex (a : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (ball a r) = Real.pi * r ^ 2 := by
  rw [measureReal_def, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr, ENNReal.coe_toReal, NNReal.coe_real_pi]
  ring

namespace RouteFlux

variable {χ : ℂ → ℝ} {lam : ℝ}

/-- The real density of the charge at the origin, at every scale. -/
noncomputable def density (χ : ℂ → ℝ) (lam : ℝ) (x : ℂ) : ℝ :=
  (lam ^ 2)⁻¹ * χ (x / (lam : ℂ))

/-- The mass enclosed by an open disc. This definition also covers nonpositive radii. -/
noncomputable def massProfile (χ : ℂ → ℝ) (lam r : ℝ) : ℝ :=
  (smearedCharge χ 0 lam).real (ball 0 r)

/-- The polar density of enclosed mass. -/
noncomputable def massDensity (χ : ℂ → ℝ) (lam r : ℝ) : ℝ :=
  2 * Real.pi * r * density χ lam (r : ℂ)

theorem massProfile_nonneg (χ : ℂ → ℝ) (lam r : ℝ) : 0 ≤ massProfile χ lam r :=
  measureReal_nonneg

theorem massProfile_mono (hχ : IsMollifier χ) (lam : ℝ) : Monotone (massProfile χ lam) := by
  have := isFiniteMeasure_smearedCharge hχ 0 lam
  exact fun _ _ hab => measureReal_mono (ball_subset_ball hab)

/-- The probability bound used in Lemma 3.1. -/
theorem massProfile_le_one (hχ : IsMollifier χ) (hlam : 0 < lam) (r : ℝ) :
    massProfile χ lam r ≤ 1 := by
  have := isProbabilityMeasure_smearedCharge hχ 0 hlam
  exact measureReal_le_one

/-- The quadratic mass bound used at the origin in Lemma 3.1. -/
theorem massProfile_le_sq (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hlam : 0 < lam) {r : ℝ} (hr : 0 ≤ r) :
    massProfile χ lam r ≤ Real.pi * M / lam ^ 2 * r ^ 2 := by
  refine (smearedCharge_real_le hχ hM hlam 0 measure_ball_lt_top.ne).trans (le_of_eq ?_)
  rw [volume_real_ball_complex 0 hr]
  ring

/-- The annulus estimate, which needs no continuity of the density. -/
theorem massProfile_sub_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hlam : 0 < lam) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    massProfile χ lam b - massProfile χ lam a ≤
      Real.pi * M / lam ^ 2 * (b ^ 2 - a ^ 2) := by
  have := isFiniteMeasure_smearedCharge hχ 0 lam
  have hs : ball (0 : ℂ) a ⊆ ball 0 b := ball_subset_ball hab
  unfold massProfile
  rw [← measureReal_sdiff hs measurableSet_ball]
  refine (smearedCharge_real_le hχ hM hlam 0
    (measure_ne_top_of_subset sdiff_subset measure_ball_lt_top.ne)).trans (le_of_eq ?_)
  rw [measureReal_sdiff hs measurableSet_ball measure_ball_lt_top.ne,
    volume_real_ball_complex 0 (ha.trans hab), volume_real_ball_complex 0 ha]
  ring

/-- Local Lipschitz continuity of the mass profile on nonnegative radii. -/
theorem lipschitzOnWith_massProfile (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hlam : 0 < lam) {R : ℝ} (hR : 0 ≤ R) :
    LipschitzOnWith (Real.toNNReal (2 * (Real.pi * M / lam ^ 2) * R))
      (massProfile χ lam) (Icc 0 R) := by
  have hM0 := hχ.nonneg_of_le hM
  have hK : 0 ≤ Real.pi * M / lam ^ 2 := by positivity
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb
  rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq]
  wlog hab : a ≤ b generalizing a b
  · simpa only [abs_sub_comm] using this b hb a ha (le_of_not_ge hab)
  rw [abs_of_nonpos (sub_nonpos.mpr (massProfile_mono hχ lam hab)),
    abs_of_nonpos (sub_nonpos.mpr hab)]
  have h := massProfile_sub_le hχ hM hlam ha.1 hab
  have hmul := mul_nonneg (mul_nonneg hK (sub_nonneg.mpr hab))
    (show 0 ≤ 2 * R - (a + b) by linarith [ha.2, hb.2])
  nlinarith

/-- Absolute continuity asserted in Lemma 3.1, for bounded measurable mollifiers. -/
theorem absolutelyContinuousOnInterval_massProfile (hχ : IsMollifier χ) (hlam : 0 < lam)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval (massProfile χ lam) a b := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  have h := (lipschitzOnWith_massProfile hχ hM hlam (ha.trans hab)).mono
    (show uIcc a b ⊆ Icc 0 b by rw [uIcc_of_le hab]; exact Icc_subset_Icc_left ha)
  exact h.absolutelyContinuousOnInterval

private theorem density_radial (hχ : IsMollifier χ) {x y : ℂ} (h : ‖x‖ = ‖y‖) :
    density χ lam x = density χ lam y := by
  unfold density
  rw [hχ.radial (x := x / (lam : ℂ)) (y := y / (lam : ℂ)) (by simp only [norm_div, h])]

private theorem measurable_density (hχ : IsMollifier χ) : Measurable (density χ lam) :=
  measurable_const.mul (hχ.measurable.comp (continuous_id.div_const _).measurable)

/-- Enclosed mass is the integral of the real density over the disc. -/
theorem massProfile_eq_integral_density (hχ : IsMollifier χ) (lam r : ℝ) :
    massProfile χ lam r = ∫ x in ball (0 : ℂ) r, density χ lam x := by
  rw [massProfile, ← integral_indicator_one measurableSet_ball,
    integral_smearedCharge hχ]
  simp only [sub_zero, smul_eq_mul, density]
  rw [← integral_indicator measurableSet_ball]
  congr 1
  ext x
  by_cases hx : x ∈ ball (0 : ℂ) r <;> simp [hx]

private theorem integrableOn_density (hχ : IsMollifier χ) (lam r : ℝ) :
    IntegrableOn (density χ lam) (ball (0 : ℂ) r) := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  apply IntegrableOn.of_bound measure_ball_lt_top (measurable_density hχ).aestronglyMeasurable
    ((lam ^ 2)⁻¹ * M)
  filter_upwards with x
  dsimp [density]
  rw [abs_of_nonneg (mul_nonneg (by positivity) (hχ.nonneg _))]
  exact mul_le_mul_of_nonneg_left (hM _) (by positivity)

/-- Polar integration identifies the mass profile with a one-dimensional primitive. -/
theorem massProfile_eq_integral_massDensity (hχ : IsMollifier χ) (lam : ℝ) {r : ℝ}
    (hr : 0 ≤ r) : massProfile χ lam r = ∫ t in (0 : ℝ)..r, massDensity χ lam t := by
  rw [massProfile_eq_integral_density hχ,
    TwoComponentCoulomb.setIntegral_ball_zero_eq_polar_of_measurable
      (measurable_density hχ) (integrableOn_density hχ lam r),
    intervalIntegral.integral_of_le hr, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have he : ∀ θ : ℝ, density χ lam (circleMap 0 t θ) = density χ lam (t : ℂ) := fun θ =>
    density_radial hχ (by simp [norm_circleMap_zero, Complex.norm_real])
  simp_rw [he]
  rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
  simp only [smul_eq_mul, massDensity]
  ring

private theorem locallyIntegrable_massDensity (hχ : IsMollifier χ) (lam : ℝ) :
    LocallyIntegrable (massDensity χ lam) volume := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  apply IntegrableOn.of_bound hK.measure_lt_top
    ((measurable_const.mul measurable_id).mul
      ((measurable_density hχ).comp Complex.continuous_ofReal.measurable)).aestronglyMeasurable
    (2 * Real.pi * R * ((lam ^ 2)⁻¹ * M))
  filter_upwards [ae_restrict_mem hK.measurableSet] with r hr
  change ‖2 * Real.pi * r * density χ lam (r : ℂ)‖ ≤ _
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi),
    Real.norm_eq_abs (density χ lam (r : ℂ)),
    abs_of_nonneg (show 0 ≤ density χ lam (r : ℂ) from mul_nonneg (by positivity) (hχ.nonneg _))]
  have hM0 := hχ.nonneg_of_le hM
  have hR0 : 0 ≤ R := (norm_nonneg r).trans (hR r hr)
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hR r hr) (by positivity))
    (mul_le_mul_of_nonneg_left (hM _) (by positivity))
    (mul_nonneg (by positivity) (hχ.nonneg _)) (by positivity)

/-- The derivative of enclosed mass exists almost everywhere and is the polar density.
This is the measurable-density version of the differentiation step in Lemma 3.1. -/
theorem ae_hasDerivAt_massProfile (hχ : IsMollifier χ) (lam : ℝ) :
    ∀ᵐ r : ℝ, 0 < r → HasDerivAt (massProfile χ lam) (massDensity χ lam r) r := by
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral (locallyIntegrable_massDensity hχ lam)] with r hr hr0
  apply (hr 0).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hr0] with t ht
  exact massProfile_eq_integral_massDensity hχ lam ht.le

/-- The almost everywhere derivative bound in Lemma 3.1. -/
theorem ae_abs_deriv_massProfile_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (lam : ℝ) : ∀ᵐ r : ℝ, 0 < r →
      |deriv (massProfile χ lam) r| ≤ 2 * Real.pi * r * (M / lam ^ 2) := by
  filter_upwards [ae_hasDerivAt_massProfile hχ lam] with r hr hr0
  have hd : 0 ≤ massDensity χ lam r :=
    mul_nonneg (by positivity) (mul_nonneg (by positivity) (hχ.nonneg _))
  rw [(hr hr0).deriv, abs_of_nonneg hd, massDensity]
  dsimp [density]
  calc 2 * Real.pi * r * ((lam ^ 2)⁻¹ * χ ((r : ℂ) / (lam : ℂ))) ≤
      2 * Real.pi * r * ((lam ^ 2)⁻¹ * M) := by gcongr; exact hM _
    _ = 2 * Real.pi * r * (M / lam ^ 2) := by ring

end RouteFlux

end MultipoleBKT

end
