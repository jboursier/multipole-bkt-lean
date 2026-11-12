/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Energy.RouteNeumann.Base
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Mixed derivatives and source translation

For (3.20),
the source derivative of the image field is uniformly bounded when the source
lies in the inner quarter disc. This is the mixed derivative of the image
logarithm. The mean value theorem gives the translation estimate.
-/

public section

open MeasureTheory Metric Set InnerProductSpace ComplexConjugate

namespace MultipoleBKT

/-- The mixed derivative of the image logarithm, written as the complex source
derivative of its spatial gradient in (3.19), as in the proof of Lemma 3.5. -/
theorem hasDerivAt_screenedImageField_source {z a w : ℂ} {τ : ℝ}
    (h : (τ : ℂ) ^ 2 - conj (w - z) * (a - z) ≠ 0) :
    HasDerivAt (fun b => screenedImageField z τ b w)
      ((τ : ℂ) ^ 2 / ((τ : ℂ) ^ 2 - conj (w - z) * (a - z)) ^ 2) a := by
  have hn := (hasDerivAt_id a).sub_const z
  have hd := (hn.const_mul (conj (w - z))).const_sub ((τ : ℂ) ^ 2)
  convert hn.div hd h using 1 <;> simp only [id_eq]
  congr 1
  ring

/-- Uniform bound for the mixed derivative on the inner quarter disc,
as in the proof of Lemma 3.5. The spatial point may reach the boundary. -/
theorem norm_deriv_screenedImageField_source_le {z a w : ℂ} {τ : ℝ}
    (hτ : 0 < τ) (hw : ‖w - z‖ ≤ τ) (ha : ‖a - z‖ ≤ τ / 4) :
    ‖deriv (fun b => screenedImageField z τ b w) a‖ ≤ 2 / τ ^ 2 := by
  have hp : ‖w - z‖ * ‖a - z‖ ≤ τ ^ 2 / 4 := by
    calc ‖w - z‖ * ‖a - z‖ ≤ τ * (τ / 4) :=
      mul_le_mul hw ha (norm_nonneg _) hτ.le
      _ = τ ^ 2 / 4 := by ring
  have hn := norm_sub_norm_le ((τ : ℂ) ^ 2) (conj (w - z) * (a - z))
  rw [norm_ofReal_sq, norm_mul, Complex.norm_conj] at hn
  have hden : 3 * τ ^ 2 / 4 ≤ ‖(τ : ℂ) ^ 2 - conj (w - z) * (a - z)‖ := by linarith
  rw [(hasDerivAt_screenedImageField_source
    (screenedImage_denom_ne_zero (by nlinarith))).deriv, norm_div, norm_ofReal_sq, norm_pow]
  calc τ ^ 2 / ‖(τ : ℂ) ^ 2 - conj (w - z) * (a - z)‖ ^ 2
      ≤ τ ^ 2 / (3 * τ ^ 2 / 4) ^ 2 :=
        div_le_div_of_nonneg_left (sq_nonneg τ) (by positivity)
          (pow_le_pow_left₀ (by positivity) hden 2)
    _ ≤ 2 / τ ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (τ ^ 2)]

/-- Translating the source changes the image field by at most its mixed
source derivative times the translation length, as in the proof of Lemma 3.5. -/
private theorem imageField_translation_derivative {z a b w : ℂ} {τ : ℝ}
    (hτ : 0 < τ) (hw : ‖w - z‖ ≤ τ)
    (ha : ‖a - z‖ ≤ τ / 4) (hb : ‖b - z‖ ≤ τ / 4) :
    ‖screenedImageField z τ b w - screenedImageField z τ a w‖ ≤
      (2 / τ ^ 2) * ‖b - a‖ := by
  apply (convex_closedBall z (τ / 4)).norm_image_sub_le_of_norm_deriv_le
    (𝕜 := ℂ) (f := fun c => screenedImageField z τ c w) (fun c hc => ?_) (fun c hc => ?_)
    (by simpa [mem_closedBall, dist_eq_norm] using ha)
    (by simpa [mem_closedBall, dist_eq_norm] using hb)
  · apply (hasDerivAt_screenedImageField_source (screenedImage_denom_ne_zero ?_)).differentiableAt
    rw [mem_closedBall, dist_eq_norm] at hc
    have := mul_le_mul hw hc (norm_nonneg (c - z)) hτ.le
    nlinarith
  · exact norm_deriv_screenedImageField_source_le hτ hw
      (by simpa [mem_closedBall, dist_eq_norm] using hc)

/-- Translation and scaling of the image field. Its spatial gradient has
one inverse power of the screening radius, as in the proof of Lemma 3.5. -/
theorem screenedImageField_rescale {τ : ℝ} (hτ : 0 < τ) (z a w : ℂ) :
    screenedImageField z τ a w = τ⁻¹ • screenedImageField 0 1
      (τ⁻¹ • (a - z)) (τ⁻¹ • (w - z)) := by
  have ht : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ.ne'
  simp only [screenedImageField, sub_zero, Complex.ofReal_one, one_pow, Complex.real_smul,
    Complex.ofReal_inv, map_mul, map_inv₀, Complex.conj_ofReal]
  by_cases hd : (τ : ℂ) ^ 2 - conj (w - z) * (a - z) = 0
  · have hd' : 1 - (τ : ℂ)⁻¹ * conj (w - z) * ((τ : ℂ)⁻¹ * (a - z)) = 0 := by
      field_simp
      linear_combination hd
    rw [hd, hd']
    simp
  · field_simp

/-- The unit-disc mixed derivative estimate transported back to the screening
disc, as in the proof of Lemma 3.5. -/
theorem norm_screenedImageField_sub_le {z a b w : ℂ} {τ : ℝ}
    (hτ : 0 < τ) (hw : ‖w - z‖ ≤ τ)
    (ha : ‖a - z‖ ≤ τ / 4) (hb : ‖b - z‖ ≤ τ / 4) :
    ‖screenedImageField z τ b w - screenedImageField z τ a w‖ ≤
      (2 / τ ^ 2) * ‖b - a‖ := by
  have hn (x : ℂ) : ‖τ⁻¹ • (x - z)‖ = ‖x - z‖ / τ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτ)]
    ring
  have hunit := imageField_translation_derivative (z := 0) (τ := 1) zero_lt_one
    (w := τ⁻¹ • (w - z)) (a := τ⁻¹ • (a - z)) (b := τ⁻¹ • (b - z))
    (by rw [sub_zero, hn, div_le_one hτ]; exact hw)
    (by rw [sub_zero, hn, div_le_iff₀ hτ]; norm_num; linarith)
    (by rw [sub_zero, hn, div_le_iff₀ hτ]; norm_num; linarith)
  rw [screenedImageField_rescale hτ z b w, screenedImageField_rescale hτ z a w,
    ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτ)]
  have he : τ⁻¹ • (b - z) - τ⁻¹ • (a - z) = τ⁻¹ • (b - a) := by
    rw [← smul_sub]
    congr 1
    ring
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτ)] at hunit
  calc _ ≤ τ⁻¹ * (2 * (τ⁻¹ * ‖b - a‖)) := by
          exact mul_le_mul_of_nonneg_left (by simpa using hunit) (inv_nonneg.mpr hτ.le)
    _ = _ := by ring

private theorem integrable_imageField_inner {μ : Measure ℂ} [IsFiniteMeasure μ]
    {z w : ℂ} {τ : ℝ} (hτ : 0 < τ) (hw : ‖w - z‖ ≤ τ)
    (hμ : ∀ᵐ a ∂μ, ‖a - z‖ ≤ τ / 4) :
    Integrable (fun a => screenedImageField z τ a w) μ := by
  have heq : μ.restrict (closedBall z (τ / 4)) = μ :=
    Measure.restrict_eq_self_of_ae_mem
      (by simpa only [mem_closedBall, dist_eq_norm] using hμ)
  have hc : ContinuousOn (fun a => screenedImageField z τ a w)
      (closedBall z (τ / 4)) := by
    intro a ha
    apply (hasDerivAt_screenedImageField_source
      (screenedImage_denom_ne_zero ?_)).continuousAt.continuousWithinAt
    rw [mem_closedBall, dist_eq_norm] at ha
    have := mul_le_mul hw ha (norm_nonneg (a - z)) hτ.le
    nlinarith
  have hi := hc.integrableOn_compact (isCompact_closedBall z (τ / 4)) (μ := μ)
  rwa [IntegrableOn, heq] at hi

/-- The translated image estimate for any probability measure supported in the
inner quarter disc whose translate also lies there, (3.20). Pull both averages back to one source variable, apply the mean value
theorem to the mixed derivative, then integrate against the unit mass. -/
theorem norm_integral_screenedImageField_translate_sub_le (μ : Measure ℂ)
    [IsProbabilityMeasure μ] {z w δ : ℂ} {τ : ℝ}
    (hτ : 0 < τ) (hw : ‖w - z‖ ≤ τ)
    (hμ : ∀ᵐ a ∂μ, ‖a - z‖ ≤ τ / 4)
    (hδ : ∀ᵐ a ∂μ, ‖a + δ - z‖ ≤ τ / 4) :
    ‖(∫ a, screenedImageField z τ a w ∂μ.map (fun a => a + δ)) -
      ∫ a, screenedImageField z τ a w ∂μ‖ ≤ (2 / τ ^ 2) * ‖δ‖ := by
  have hi₀ := integrable_imageField_inner hτ hw hμ
  have hi := integrable_imageField_inner (μ := μ.map (fun a => a + δ)) hτ hw
    ((measurableEmbedding_addRight δ).ae_map_iff.mpr hδ)
  have hi' : Integrable (fun a => screenedImageField z τ (a + δ) w) μ :=
    (measurableEmbedding_addRight δ).integrable_map_iff.mp hi
  rw [(measurableEmbedding_addRight δ).integral_map, ← integral_sub hi' hi₀]
  calc _ ≤ ((2 / τ ^ 2) * ‖δ‖) * μ.real univ := by
          apply norm_integral_le_of_norm_le_const
          filter_upwards [hμ, hδ] with a ha hshift
          simpa only [add_sub_cancel_left] using
            norm_screenedImageField_sub_le hτ hw ha hshift
    _ = _ := by simp

end MultipoleBKT
