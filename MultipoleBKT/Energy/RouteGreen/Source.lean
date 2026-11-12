/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Energy.RouteGreen.Kernel
public import MultipoleBKT.Energy.RouteGreen.ImageSource
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import TwoComponentCoulomb.Potential.Fundamental

/-!
# The source equation and its compensating density

For the displayed kernel (3.19), the equation
`-Δ G = 2π (δ_y - 1/π)` is tested against compactly supported `C¹` functions.
The left hand side is the negative distributional divergence of `field`:
`∫ Dξ(x)[field x y]`. This first order weak formulation includes the singular
source and does not assert a classical Laplacian at the pole.

The logarithmic pole gives `2π ξ(y)`. The image charge lies outside the test
support and contributes zero. The quadratic compensator has gradient `x`
and contributes `-2 ∫ ξ` by integration by parts in the two real coordinates.
-/

@[expose] public section

open MeasureTheory Metric Set InnerProductSpace ComplexConjugate

namespace MultipoleBKT.RouteGreen

private theorem integrable_coordinate_test {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ)
    (hc : HasCompactSupport ξ) (l : ℂ →L[ℝ] ℝ) (v : ℂ) :
    Integrable fun w => l w * fderiv ℝ ξ w v := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact l.continuous.mul ((hξ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  · exact (hc.fderiv_apply ℝ v).mul_left

private theorem integral_coordinate_test {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ)
    (hc : HasCompactSupport ξ) (l : ℂ →L[ℝ] ℝ) (v : ℂ) :
    ∫ w, l w * fderiv ℝ ξ w v = -(l v * ∫ w, ξ w) := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun w => l w) (g := ξ) (v := v)
    (by simpa only [l.fderiv] using (hξ.continuous.integrable_of_hasCompactSupport hc).const_mul (l v))
    (integrable_coordinate_test hξ hc l v)
    ((l.continuous.mul hξ.continuous).integrable_of_hasCompactSupport hc.mul_left)
    (fun _ _ => l.differentiableAt) (fun w _ => hξ.differentiable one_ne_zero w)
  simpa only [l.fderiv, integral_const_mul] using h

/-- Integrability of the compensator tested against `∇ξ`, equation (3.19). -/
theorem integrable_compensator_test {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ)
    (hc : HasCompactSupport ξ) (z : ℂ) :
    Integrable fun w => fderiv ℝ ξ w (w - z) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (hξ.continuous_fderiv one_ne_zero).clm_apply (continuous_id.sub continuous_const)
  · refine HasCompactSupport.intro hc.isCompact ?_
    intro w hw
    simp [fderiv_of_notMem_tsupport ℝ hw]

/-- The quadratic term has constant Laplacian `2`, equation (3.19), expressed by testing its gradient against `∇ξ`. -/
theorem integral_compensator_test {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ)
    (hc : HasCompactSupport ξ) :
    ∫ w, fderiv ℝ ξ w w = -2 * ∫ w, ξ w := by
  have he (w : ℂ) : fderiv ℝ ξ w w =
      w.re * fderiv ℝ ξ w 1 + w.im * fderiv ℝ ξ w Complex.I := by
    calc fderiv ℝ ξ w w = fderiv ℝ ξ w (w.re • (1 : ℂ) + w.im • Complex.I) := by
           congr 1
           simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im w).symm
      _ = _ := by rw [map_add, map_smul, map_smul]; rfl
  simp_rw [he]
  have hadd := integral_add (integrable_coordinate_test hξ hc Complex.reCLM 1)
    (integrable_coordinate_test hξ hc Complex.imCLM Complex.I)
  have hr := integral_coordinate_test hξ hc Complex.reCLM 1
  have hi := integral_coordinate_test hξ hc Complex.imCLM Complex.I
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hadd hr hi
  rw [hadd, hr, hi]
  simp
  ring

/-- The compensating density of the Green problem preceding (3.19) has mass one. -/
theorem integral_density : ∫ _ : ℂ in ball 0 1, density = 1 := by
  rw [setIntegral_const, smul_eq_mul, volume_real_ball_complex 0 (by norm_num)]
  simp [density, Real.pi_ne_zero]

/-- The quadratic term contributes exactly the constant density of the
Green problem preceding (3.19). -/
theorem compensator_density {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ)
    (hc : HasCompactSupport ξ) :
    ∫ w, fderiv ℝ ξ w w = -2 * Real.pi * ∫ w, density * ξ w := by
  rw [integral_compensator_test hξ hc, integral_const_mul]
  unfold density
  field_simp

/-- The distributional equation of the Green problem preceding (3.19). The test function is compactly supported inside the
disc. The field is the derivative of `kernel` away from its pole by
`hasFDerivAt_kernel`. The left side means negative distributional divergence,
not a pointwise Laplacian at `y`. -/
theorem source {y : ℂ} (hy : ‖y‖ < 1) {ξ : ℂ → ℝ}
    (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ)
    (hs : tsupport ξ ⊆ ball 0 1) :
    ∫ w, fderiv ℝ ξ w (field w y) =
      2 * Real.pi * (ξ y - ∫ w, density * ξ w) := by
  have hp : Integrable fun w => fderiv ℝ ξ w
      (-((‖w - y‖ ^ 2)⁻¹ : ℝ) • (w - y)) := by
    have ht := (TwoComponentCoulomb.integrable_fderiv_apply_gradLogKernel_zero
      (hξ.comp (contDiff_const.add contDiff_id))
      (hc.comp_isClosedEmbedding (Homeomorph.addLeft y).isClosedEmbedding)).comp_sub_right y
    refine ht.congr (Filter.Eventually.of_forall fun w => ?_)
    exact (TwoComponentCoulomb.fderiv_apply_gradLogKernel_translate y w).symm
  have hi := integrable_fderiv_apply_screenedImageField hξ hc 0 1 y
  have hq := integrable_compensator_test hξ hc 0
  simp only [sub_zero] at hq
  have himage : y ≠ 0 → ξ (imagePoint 0 1 y) = 0 := by
    intro hy0
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have hn := hs hm
    rw [mem_ball, dist_eq_norm, sub_zero] at hn
    have he := norm_imagePoint_sub 0 1 y
    simp only [sub_zero, one_pow] at he
    rw [he] at hn
    have hypos := norm_pos_iff.2 hy0
    have : 1 < ‖y‖ := by simpa using (div_lt_iff₀ hypos).1 hn
    linarith
  simp only [field, map_add]
  have hadd := integral_add (hp.add hi) hq
  have hadd' := integral_add hp hi
  simp only [Pi.add_apply] at hadd hadd'
  rw [hadd, hadd',
    TwoComponentCoulomb.integral_fderiv_apply_gradLogKernel hξ hc,
    integral_fderiv_apply_screenedImageField hξ hc 0 1 y himage,
    compensator_density hξ hc]
  ring

/-- The centered source is included directly in (3.19). Its source equation has the same compensating density. -/
theorem source_center {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ)
    (hc : HasCompactSupport ξ) (hs : tsupport ξ ⊆ ball 0 1) :
    ∫ w, fderiv ℝ ξ w (-((‖w‖ ^ 2)⁻¹ : ℝ) • w + w) =
      2 * Real.pi * (ξ 0 - ∫ w, density * ξ w) := by
  simpa only [field_center] using source (y := 0) (by simp) hξ hc hs

end MultipoleBKT.RouteGreen
