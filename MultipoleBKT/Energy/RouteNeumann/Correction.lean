/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Energy.RouteNeumann.WeakGradient
public import MultipoleBKT.Energy.RouteNeumann.SmearedCorrection

/-!
# The translated correction

The harmonic correction problem (3.23) and the translated smeared-image
estimate (3.20) of the paper.
-/

public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace ComplexConjugate
open scoped ContDiff

namespace MultipoleBKT.RouteNeumann

variable {χ : ℂ → ℝ} {lam τ : ℝ} {d : ℂ × ℂ}

/-- The correction is weakly harmonic inside the screening disc,
(3.23). -/
theorem correction_harmonic (hlam : 0 < lam) (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ)
    {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ)
    (hs : tsupport ξ ⊆ ball (dipoleMidpoint d) τ) :
    ∫ w, fderiv ℝ ξ w (screenedCorrectionField τ d w) = 0 := by
  have ht := pos_of_screening hlam hτ
  have hr := norm_le_of_screening hτ
  have himage : ∀ a, ‖a - dipoleMidpoint d‖ = ‖d.2 - d.1‖ / 2 →
      a ≠ dipoleMidpoint d → ξ (imagePoint (dipoleMidpoint d) τ a) = 0 := by
    intro a ha hne
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have hn := hs hmem
    rw [mem_ball, dist_eq_norm, norm_imagePoint_sub] at hn
    have ha0 : 0 < ‖a - dipoleMidpoint d‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    rw [div_lt_iff₀ ha0, ha] at hn
    nlinarith
  simp only [screenedCorrectionField, map_sub]
  rw [integral_sub (integrable_fderiv_apply_screenedImageField hξ hc _ _ _)
    (integrable_fderiv_apply_screenedImageField hξ hc _ _ _),
    integral_fderiv_apply_screenedImageField hξ hc _ _ _
      (himage _ (norm_fst_sub_dipoleMidpoint d)),
    integral_fderiv_apply_screenedImageField hξ hc _ _ _
      (himage _ (norm_snd_sub_dipoleMidpoint d)), sub_self]

/-- The correction has the negative free-field normal derivative,
(3.23). -/
theorem correction_normal_derivative (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) {w : ℂ}
    (hw : ‖w - dipoleMidpoint d‖ = τ) :
    inner ℝ (τ⁻¹ • (w - dipoleMidpoint d)) (screenedCorrectionField τ d w) =
      inner ℝ (τ⁻¹ • (w - dipoleMidpoint d))
        (((‖w - d.1‖ ^ 2)⁻¹ : ℝ) • (w - d.1) -
          ((‖w - d.2‖ ^ 2)⁻¹ : ℝ) • (w - d.2)) := by
  have ht := pos_of_screening hlam hτ
  have hw' : τ / 2 ≤ ‖w - dipoleMidpoint d‖ := by rw [hw]; linarith
  have h1 := lam_lt_norm_sub_of_screening hlam hτ (norm_fst_sub_dipoleMidpoint d) hw'
  have h2 := lam_lt_norm_sub_of_screening hlam hτ (norm_snd_sub_dipoleMidpoint d) hw'
  have hz := inner_screenedField_eq_zero hχ hlam hτ hw
  rw [screenedField, dipoleField, smearedField_of_lt hχ hlam h1,
    smearedField_of_lt hχ hlam h2, inner_add_right, inner_sub_right] at hz
  simp only [real_inner_smul_left, inner_sub_right, real_inner_smul_right] at hz ⊢
  linear_combination τ⁻¹ * hz

/-- The concrete representative is smooth on a neighborhood of each boundary
point, since both sources are strictly inside the disc, equation (3.19). -/
theorem contDiffAt_screenedPotential_near_boundary (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) {w : ℂ}
    (hw : ‖w - dipoleMidpoint d‖ = τ) :
    ContDiffAt ℝ ∞ (screenedPotential χ lam τ d) w := by
  have ht := pos_of_screening hlam hτ
  have hw' : τ / 2 ≤ ‖w - dipoleMidpoint d‖ := by rw [hw]; linarith
  have h1 := lam_lt_norm_sub_of_screening hlam hτ (norm_fst_sub_dipoleMidpoint d) hw'
  have h2 := lam_lt_norm_sub_of_screening hlam hτ (norm_snd_sub_dipoleMidpoint d) hw'
  have hpot (a : ℂ) (ha : lam < ‖w - a‖) :
      ContDiffAt ℝ ∞ (fun x => ∫ v, TwoComponentCoulomb.logKernel (x - v)
        ∂smearedCharge χ a lam) w := by
    have he : (fun x => ∫ v, TwoComponentCoulomb.logKernel (x - v)
        ∂smearedCharge χ a lam) =ᶠ[𝓝 w] fun x => TwoComponentCoulomb.logKernel (x - a) := by
      have hn := (isOpen_lt continuous_const
        ((continuous_id.sub continuous_const).norm)).mem_nhds ha
      filter_upwards [hn] with x hx
      exact integral_logKernel_sub_smearedCharge_of_le hχ hlam hx.le
    have hn : w - a ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (hlam.trans ha))
    have hlog : ContDiffAt ℝ ∞ (fun x : ℂ => TwoComponentCoulomb.logKernel (x - a)) w :=
      ((((contDiffAt_norm ℝ hn).comp w (contDiff_id.sub contDiff_const).contDiffAt).log
        (norm_ne_zero_iff.mpr hn)).neg)
    exact hlog.congr_of_eventuallyEq he
  have him (a : ℂ) (ha : (τ : ℂ) ^ 2 - (w - dipoleMidpoint d) *
      conj (a - dipoleMidpoint d) ≠ 0) :
      ContDiffAt ℝ ∞ (screenedImagePotential (dipoleMidpoint d) τ a) w := by
    have hp : ContDiff ℝ ∞ (fun x : ℂ => (τ : ℂ) ^ 2 -
        (x - dipoleMidpoint d) * conj (a - dipoleMidpoint d)) := by fun_prop
    exact (((contDiffAt_norm ℝ ha).comp w hp.contDiffAt).log (norm_ne_zero_iff.mpr ha)).neg
  obtain ⟨hd1, hd2⟩ := mul_norm_lt_of_screening hlam hτ (w := w) (by rw [hw]; linarith)
  exact ((hpot d.1 h1).sub (hpot d.2 h2)).add
    ((him d.1 (screenedImagePotential_arg_ne_zero hd1)).sub
      (him d.2 (screenedImagePotential_arg_ne_zero hd2)))

end MultipoleBKT.RouteNeumann
