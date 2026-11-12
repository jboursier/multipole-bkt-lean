/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Energy.RouteNeumann.Average

/-!
# The correction bound through smeared translation

The mixed derivative bound is integrated against translated smeared charges,
as in (3.20).
-/

public section

open MeasureTheory Metric Set InnerProductSpace

namespace MultipoleBKT.RouteNeumann

variable {χ : ℂ → ℝ} {lam τ : ℝ} {d : ℂ × ℂ}

/-- The correction estimate obtained by translating the smeared source,
then integrating the mixed derivative bound, as in the proof of Lemma 3.5. -/
theorem norm_correction_via_smeared_translation (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) {w : ℂ}
    (hw : ‖w - dipoleMidpoint d‖ ≤ τ) :
    ‖screenedCorrectionField τ d w‖ ≤ 2 * ‖d.2 - d.1‖ / τ ^ 2 := by
  have ht := pos_of_screening hlam hτ
  have hr := norm_le_of_screening hτ
  have hl := lam_le_of_screening hτ
  have ha : ‖d.1 - dipoleMidpoint d‖ + lam ≤ τ / 4 := by
    rw [norm_fst_sub_dipoleMidpoint]
    linarith
  have hb : ‖d.2 - dipoleMidpoint d‖ + lam ≤ τ / 4 := by
    rw [norm_snd_sub_dipoleMidpoint]
    linarith
  have h := norm_integral_screenedImageField_sub_le hχ hlam ht hw ha hb
  rw [integral_screenedImageField_smearedCharge hχ hlam ht hw
    (hb.trans_lt (by linarith : τ / 4 < τ)),
    integral_screenedImageField_smearedCharge hχ hlam ht hw
      (ha.trans_lt (by linarith : τ / 4 < τ)), norm_sub_rev] at h
  simpa only [screenedCorrectionField, div_mul_eq_mul_div] using h

/-- The uniform unit-disc density is an admissible radial mollifier.
It supplies a smeared source for the mollifier-independent correction bound. -/
theorem isMollifier_unitDisc :
    IsMollifier ((ball (0 : ℂ) 1).indicator fun _ => Real.pi⁻¹) := by
  classical
  refine ⟨measurable_const.indicator measurableSet_ball, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact indicator_nonneg (fun _ _ => inv_nonneg.mpr Real.pi_pos.le) x
  · intro x y hxy
    simp only [mem_ball_zero_iff, indicator_apply]
    rw [hxy]
  · refine ⟨Real.pi⁻¹, ?_⟩
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ ball (0 : ℂ) 1
    · simp only [indicator_of_mem hx, le_refl]
    · simp only [indicator_of_notMem hx]
      positivity
  · intro x hx
    exact indicator_of_notMem (by simpa only [mem_ball_zero_iff] using not_lt.mpr hx.le) _
  · rw [integral_indicator measurableSet_ball, setIntegral_const, smul_eq_mul,
      volume_real_ball_complex 0 (by norm_num)]
    simp [Real.pi_ne_zero]

end MultipoleBKT.RouteNeumann
