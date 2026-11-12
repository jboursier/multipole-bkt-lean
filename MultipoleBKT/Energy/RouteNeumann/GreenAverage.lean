/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Energy.RouteGreen.Kernel
public import MultipoleBKT.Energy.RouteNeumann.Average

/-!
# The Green average of a dipole source

The representation after (3.19) integrates the displayed Green kernel against the
neutral smeared source. Radial averaging identifies its image term with the
existing correction. The logarithmic scaling constants and the quadratic
compensator cancel because each charge has mass one.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace ComplexConjugate
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT.RouteNeumann

variable {χ : ℂ → ℝ} {lam τ : ℝ}

private theorem integrable_logKernel_left (hχ : IsMollifier χ) (x a : ℂ) :
    Integrable (fun v => logKernel (x - v)) (smearedCharge χ a lam) := by
  simpa only [logKernel, norm_sub_rev] using
    integrable_logKernel_sub_smearedCharge hχ x a lam

/-- The average of the displayed unit-disc Green kernel, transported to the
screening disc, equation (3.19). -/
noncomputable def greenAverage (χ : ℂ → ℝ) (lam τ : ℝ) (d : ℂ × ℂ) (w : ℂ) : ℝ :=
  (∫ v, RouteGreen.kernel (τ⁻¹ • (w - dipoleMidpoint d))
    (τ⁻¹ • (v - dipoleMidpoint d)) ∂smearedCharge χ d.1 lam) -
  ∫ v, RouteGreen.kernel (τ⁻¹ • (w - dipoleMidpoint d))
    (τ⁻¹ • (v - dipoleMidpoint d)) ∂smearedCharge χ d.2 lam

private theorem imagePotential_source_decomposition {z w v : ℂ} (hw : w ≠ z)
    (hv : imagePoint z τ w ≠ v) :
    screenedImagePotential z τ v w = logKernel (imagePoint z τ w - v) - Real.log ‖w - z‖ := by
  have hw0 := sub_ne_zero.2 hw
  have he : (τ : ℂ) ^ 2 - (w - z) * conj (v - z) =
      (w - z) * conj (imagePoint z τ w - v) := by
    simp only [imagePoint, map_sub, map_add, map_div₀, map_pow,
      Complex.conj_ofReal, Complex.conj_conj]
    field_simp
    ring
  rw [screenedImagePotential, he, norm_mul, Complex.norm_conj,
    Real.log_mul (norm_ne_zero_iff.mpr hw0) (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hv)),
    logKernel]
  ring

/-- Radial mean value for the image logarithm, as in the proof of Lemma 3.5.
The potential is smooth throughout the source disc. -/
theorem integral_screenedImagePotential_smearedCharge (hχ : IsMollifier χ) (hlam : 0 < lam)
    {z a w : ℂ} (hτ : 0 < τ) (hw : ‖w - z‖ ≤ τ)
    (ha : ‖a - z‖ + lam < τ) :
    ∫ v, screenedImagePotential z τ v w ∂smearedCharge χ a lam =
      screenedImagePotential z τ a w := by
  let := isProbabilityMeasure_smearedCharge hχ a hlam
  by_cases hwz : w = z
  · subst w
    simp [screenedImagePotential]
  have hp : lam < ‖imagePoint z τ w - a‖ := by
    have hw0 : 0 < ‖w - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hwz)
    have hnorm := norm_sub_le_norm_sub_add_norm_sub (imagePoint z τ w) a z
    have hfar : τ ≤ ‖imagePoint z τ w - z‖ := by
      rw [norm_imagePoint_sub, le_div_iff₀ hw0]
      nlinarith
    linarith
  have hpa : imagePoint z τ w ≠ a := by
    intro he
    simp only [he, sub_self, norm_zero] at hp
    linarith
  have he : (fun v => screenedImagePotential z τ v w) =ᵐ[smearedCharge χ a lam]
      fun v => logKernel (imagePoint z τ w - v) - Real.log ‖w - z‖ := by
    filter_upwards [ae_mem_closedBall_smearedCharge hχ hlam] with v hv
    apply imagePotential_source_decomposition hwz
    intro he
    rw [mem_closedBall, dist_eq_norm, ← he] at hv
    linarith
  rw [integral_congr_ae he, integral_sub
    (integrable_logKernel_left hχ _ _) (integrable_const _),
    integral_const, probReal_univ, one_smul,
    integral_logKernel_sub_smearedCharge_of_le hχ hlam hp.le,
    imagePotential_source_decomposition hwz hpa]

/-- The rescaling constants in (3.19). The pole is excluded only in this pointwise logarithmic identity. -/
theorem kernel_scaled_decomposition {z w v : ℂ} (hτ : 0 < τ) (hwv : w ≠ v)
    (hi : (τ : ℂ) ^ 2 - (w - z) * conj (v - z) ≠ 0) :
    RouteGreen.kernel (τ⁻¹ • (w - z)) (τ⁻¹ • (v - z)) =
      logKernel (w - v) + screenedImagePotential z τ v w +
        (3 * Real.log τ + ‖τ⁻¹ • (w - z)‖ ^ 2 / 2) := by
  have ht : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ.ne'
  have he1 : τ⁻¹ • (w - z) - τ⁻¹ • (v - z) = (w - v) / (τ : ℂ) := by
    simp only [Complex.real_smul, Complex.ofReal_inv]
    field_simp
    ring
  have he2 : 1 - (τ⁻¹ • (w - z)) * conj (τ⁻¹ • (v - z)) =
      ((τ : ℂ) ^ 2 - (w - z) * conj (v - z)) / (τ : ℂ) ^ 2 := by
    simp only [Complex.real_smul, map_mul, Complex.conj_ofReal,
      Complex.ofReal_inv, map_inv₀]
    field_simp
  rw [RouteGreen.kernel, he1, he2, norm_div, norm_div, norm_ofReal_sq,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ,
    Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hwv)) hτ.ne',
    Real.log_div (norm_ne_zero_iff.mpr hi) (pow_ne_zero 2 hτ.ne'),
    Real.log_pow, logKernel, screenedImagePotential]
  ring

/-- The Green average is exactly the existing screened potential on the
closed screening disc, equation (3.19). -/
theorem greenAverage_eq_screenedPotential (hχ : IsMollifier χ) (hlam : 0 < lam)
    {d : ℂ × ℂ} (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) {w : ℂ}
    (hw : ‖w - dipoleMidpoint d‖ ≤ τ) :
    greenAverage χ lam τ d w = screenedPotential χ lam τ d w := by
  have ht := pos_of_screening hlam hτ
  have hr := norm_le_of_screening hτ
  have hl := lam_le_of_screening hτ
  have havg : ∀ a, ‖a - dipoleMidpoint d‖ = ‖d.2 - d.1‖ / 2 →
      (∫ v, RouteGreen.kernel (τ⁻¹ • (w - dipoleMidpoint d))
        (τ⁻¹ • (v - dipoleMidpoint d)) ∂smearedCharge χ a lam) =
      (∫ v, logKernel (w - v) ∂smearedCharge χ a lam) +
        screenedImagePotential (dipoleMidpoint d) τ a w +
        (3 * Real.log τ + ‖τ⁻¹ • (w - dipoleMidpoint d)‖ ^ 2 / 2) := by
    intro a ha
    have hinner : ‖a - dipoleMidpoint d‖ + lam < τ := by rw [ha]; linarith
    let := isProbabilityMeasure_smearedCharge hχ a hlam
    have him : Integrable (fun v => screenedImagePotential (dipoleMidpoint d) τ v w)
        (smearedCharge χ a lam) := by
      apply integrable_on_source_disc hχ hlam
      intro v hv
      have hvz := norm_sub_le_norm_sub_add_norm_sub v a (dipoleMidpoint d)
      rw [mem_closedBall, dist_eq_norm] at hv
      have hn : (τ : ℂ) ^ 2 - (w - dipoleMidpoint d) * conj (v - dipoleMidpoint d) ≠ 0 := by
        apply screenedImagePotential_arg_ne_zero
        have := mul_le_mul_of_nonneg_right hw (norm_nonneg (v - dipoleMidpoint d))
        nlinarith
      exact (((by fun_prop : ContinuousAt (fun v : ℂ =>
        (τ : ℂ) ^ 2 - (w - dipoleMidpoint d) * conj (v - dipoleMidpoint d)) v).norm.log
          (norm_ne_zero_iff.mpr hn)).neg).continuousWithinAt
    have he : (fun v => RouteGreen.kernel (τ⁻¹ • (w - dipoleMidpoint d))
        (τ⁻¹ • (v - dipoleMidpoint d))) =ᵐ[smearedCharge χ a lam]
        fun v => logKernel (w - v) + screenedImagePotential (dipoleMidpoint d) τ v w +
          (3 * Real.log τ + ‖τ⁻¹ • (w - dipoleMidpoint d)‖ ^ 2 / 2) := by
      filter_upwards [ae_ne_smearedCharge χ a w lam,
        ae_mem_closedBall_smearedCharge hχ hlam] with v hv hvb
      apply kernel_scaled_decomposition ht hv.symm
      apply screenedImagePotential_arg_ne_zero
      rw [mem_closedBall, dist_eq_norm] at hvb
      have hvz := norm_sub_le_norm_sub_add_norm_sub v a (dipoleMidpoint d)
      have := mul_le_mul_of_nonneg_right hw (norm_nonneg (v - dipoleMidpoint d))
      nlinarith
    have hip : Integrable (fun v => logKernel (w - v) +
        screenedImagePotential (dipoleMidpoint d) τ v w) (smearedCharge χ a lam) :=
      (integrable_logKernel_left hχ w a).add him
    rw [integral_congr_ae he, integral_add hip (integrable_const _),
      integral_add (integrable_logKernel_left hχ w a) him,
      integral_screenedImagePotential_smearedCharge hχ hlam ht hw hinner,
      integral_const, probReal_univ, one_smul]
  rw [greenAverage, havg _ (norm_fst_sub_dipoleMidpoint d),
    havg _ (norm_snd_sub_dipoleMidpoint d), screenedPotential, dipolePotential, screenedCorrection]
  ring

/-- The concrete screened field is the gradient of the Green average in the
open disc, equation (3.19). -/
theorem hasGradientAt_greenAverage (hχ : IsMollifier χ) (hlam : 0 < lam)
    {d : ℂ × ℂ} (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) {w : ℂ}
    (hw : w ∈ ball (dipoleMidpoint d) τ) :
    HasGradientAt (greenAverage χ lam τ d) (screenedField χ lam τ d w) w := by
  have ht := pos_of_screening hlam hτ
  have hw' : ‖w - dipoleMidpoint d‖ < 2 * τ := by
    rw [mem_ball, dist_eq_norm] at hw
    linarith
  apply (hasGradientAt_screenedPotential hχ hlam hτ hw').congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds hw] with v hv
  exact greenAverage_eq_screenedPotential hχ hlam hτ (by simpa only [dist_eq_norm] using (mem_ball.mp hv).le)

end MultipoleBKT.RouteNeumann
