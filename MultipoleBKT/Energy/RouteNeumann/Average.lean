/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Energy.RouteNeumann.Translation
import TwoComponentCoulomb.Potential.DiscField

/-!
# Averaging image charges

In the proof of Lemma 3.5, the image term of (3.19) is averaged against radial
smeared charges. Newton's theorem
in the source variable identifies this average with the existing image field.
-/

public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace ComplexConjugate
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT

variable {χ : ℂ → ℝ} {lam τ : ℝ}

/-- Integration of a continuous function on the support of a smeared charge. -/
theorem RouteNeumann.integrable_on_source_disc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hχ : IsMollifier χ) (hlam : 0 < lam) {a : ℂ} {f : ℂ → E}
    (hf : ContinuousOn f (closedBall a lam)) : Integrable f (smearedCharge χ a lam) := by
  let := isProbabilityMeasure_smearedCharge hχ a hlam
  have heq : (smearedCharge χ a lam).restrict (closedBall a lam) = smearedCharge χ a lam :=
    Measure.restrict_eq_self_of_ae_mem (ae_mem_closedBall_smearedCharge hχ hlam)
  have hi := hf.integrableOn_compact (isCompact_closedBall a lam)
    (μ := smearedCharge χ a lam)
  rwa [IntegrableOn, heq] at hi

/-- The first moment of a radial charge is its center. This includes a source
at the center of the screening disc. -/
theorem integral_id_smearedCharge (hχ : IsMollifier χ) (hlam : 0 < lam) (a : ℂ) :
    ∫ v, v ∂smearedCharge χ a lam = a := by
  let := isProbabilityMeasure_smearedCharge hχ a hlam
  have hi : Integrable (fun v : ℂ => v - a) (smearedCharge χ a lam) :=
    RouteNeumann.integrable_on_source_disc hχ hlam
      (continuous_id.sub continuous_const).continuousOn
  have hr := integral_comp_rotate_smearedCharge' hχ a lam
    (u := -1) (by simp) (fun v => v - a)
  have he : (fun v : ℂ => a + -1 * (v - a) - a) = fun v => -(v - a) := by
    funext v
    ring
  rw [he, integral_neg] at hr
  have hz : ∫ v, (v - a) ∂smearedCharge χ a lam = 0 := by
    have hre := congrArg Complex.re hr
    have him := congrArg Complex.im hr
    apply Complex.ext <;> simp only [Complex.neg_re, Complex.neg_im, Complex.zero_re,
      Complex.zero_im] at * <;> linarith
  have hid : Integrable (fun v : ℂ => v) (smearedCharge χ a lam) :=
    RouteNeumann.integrable_on_source_disc hχ hlam continuous_id.continuousOn
  rw [integral_sub hid (integrable_const a), integral_const, probReal_univ, one_smul] at hz
  exact sub_eq_zero.mp hz

/-- Viewing the image field as a function of its source gives a logarithmic
point field outside the source disc, plus a constant. -/
private theorem imageField_source_decomposition {z w a : ℂ} {τ : ℝ}
    (hw : w ≠ z) (ha : (τ : ℂ) ^ 2 - conj (w - z) * (a - z) ≠ 0) :
    screenedImageField z τ a w = -(conj (w - z))⁻¹ -
      ((τ : ℂ) ^ 2 / (conj (w - z)) ^ 2) *
        conj (-((‖imagePoint z τ w - a‖ ^ 2)⁻¹ : ℝ) • (imagePoint z τ w - a)) := by
  have hc : conj (w - z) ≠ 0 := (map_ne_zero _).2 (sub_ne_zero.2 hw)
  rw [TwoComponentCoulomb.gradLogKernel_eq_neg_conj_inv]
  simp only [map_neg, map_inv₀, Complex.conj_conj]
  unfold screenedImageField imagePoint
  have hd : z + (τ : ℂ) ^ 2 / conj (w - z) - a ≠ 0 := by
    intro h
    apply ha
    field_simp at h
    linear_combination h
  have he : z * conj (w - z) + (τ : ℂ) ^ 2 - a * conj (w - z) ≠ 0 := by
    convert ha using 1
    ring
  have he2 : (τ : ℂ) ^ 2 - (a - z) * conj (w - z) ≠ 0 := by
    simpa [mul_comm] using ha
  field_simp [hc, ha, hd, he, he2]
  ring

/-- Averaging the spatial image field over a radial source gives its value at
the source center, as in the proof of Lemma 3.5. -/
theorem integral_screenedImageField_smearedCharge (hχ : IsMollifier χ) (hlam : 0 < lam)
    {z a w : ℂ} (hτ : 0 < τ) (hw : ‖w - z‖ ≤ τ)
    (ha : ‖a - z‖ + lam < τ) :
    ∫ v, screenedImageField z τ v w ∂smearedCharge χ a lam =
      screenedImageField z τ a w := by
  let := isProbabilityMeasure_smearedCharge hχ a hlam
  by_cases hwz : w = z
  · subst w
    simp only [screenedImageField, sub_self, map_zero, zero_mul, sub_zero]
    have hid : Integrable (fun v : ℂ => v) (smearedCharge χ a lam) :=
      RouteNeumann.integrable_on_source_disc hχ hlam continuous_id.continuousOn
    rw [integral_div, integral_sub hid
      (integrable_const z), integral_id_smearedCharge hχ hlam,
      integral_const, probReal_univ, one_smul]
  have hp : lam < ‖imagePoint z τ w - a‖ := by
    have hw0 : 0 < ‖w - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hwz)
    have hnorm := norm_sub_le_norm_sub_add_norm_sub (imagePoint z τ w) a z
    have hfar : τ ≤ ‖imagePoint z τ w - z‖ := by
      rw [norm_imagePoint_sub, le_div_iff₀ hw0]
      nlinarith
    linarith
  have hden : ∀ v ∈ closedBall a lam,
      (τ : ℂ) ^ 2 - conj (w - z) * (v - z) ≠ 0 := by
    intro v hv
    rw [mem_closedBall, dist_eq_norm] at hv
    apply screenedImage_denom_ne_zero
    have hvz := norm_sub_le_norm_sub_add_norm_sub v a z
    have := mul_le_mul_of_nonneg_right hw (norm_nonneg (v - z))
    nlinarith
  have hda : (τ : ℂ) ^ 2 - conj (w - z) * (a - z) ≠ 0 :=
    hden a (mem_closedBall_self hlam.le)
  have hi := integrable_gradLogKernel_sub_smearedCharge hχ (imagePoint z τ w) a hlam
  have hic : Integrable (fun v => conj
      (-((‖imagePoint z τ w - v‖ ^ 2)⁻¹ : ℝ) • (imagePoint z τ w - v)))
      (smearedCharge χ a lam) :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hi
  have he : (fun v => screenedImageField z τ v w) =ᵐ[smearedCharge χ a lam]
      fun v => -(conj (w - z))⁻¹ - ((τ : ℂ) ^ 2 / (conj (w - z)) ^ 2) *
        conj (-((‖imagePoint z τ w - v‖ ^ 2)⁻¹ : ℝ) • (imagePoint z τ w - v)) := by
    filter_upwards [ae_mem_closedBall_smearedCharge hχ hlam] with v hv
    exact imageField_source_decomposition hwz (hden v hv)
  rw [integral_congr_ae he, integral_sub (integrable_const _) (hic.const_mul _),
    integral_const, probReal_univ, one_smul, integral_const_mul, integral_conj,
    integral_gradLogKernel_sub_smearedCharge hχ _ _ hlam, smearedField_of_lt hχ hlam hp]
  exact (imageField_source_decomposition hwz hda).symm

/-- The translated smeared image estimate of (3.20). Both charges are expressed using the same source variable, then
the mixed derivative bound is integrated against a probability measure. -/
theorem norm_integral_screenedImageField_sub_le (hχ : IsMollifier χ) (hlam : 0 < lam)
    {z a b w : ℂ} (hτ : 0 < τ) (hw : ‖w - z‖ ≤ τ)
    (ha : ‖a - z‖ + lam ≤ τ / 4) (hb : ‖b - z‖ + lam ≤ τ / 4) :
    ‖(∫ v, screenedImageField z τ v w ∂smearedCharge χ b lam) -
      ∫ v, screenedImageField z τ v w ∂smearedCharge χ a lam‖ ≤
      (2 / τ ^ 2) * ‖b - a‖ := by
  let := isProbabilityMeasure_smearedCharge hχ a hlam
  have ht : a + (b - a) = b := by ring
  have hm := map_add_right_smearedCharge χ a (b - a) lam
  rw [ht] at hm
  rw [← hm]
  apply norm_integral_screenedImageField_translate_sub_le _ hτ hw
  · filter_upwards [ae_mem_closedBall_smearedCharge hχ hlam] with v hv
    rw [mem_closedBall, dist_eq_norm] at hv
    exact (norm_sub_le_norm_sub_add_norm_sub v a z).trans (by linarith)
  · filter_upwards [ae_mem_closedBall_smearedCharge hχ hlam] with v hv
    rw [mem_closedBall, dist_eq_norm] at hv
    have h2 : ‖v + (b - a) - z‖ ≤ ‖v - a‖ + ‖b - z‖ := by
      convert norm_add_le (v - a) (b - z) using 1
      congr 1
      ring
    linarith

end MultipoleBKT
