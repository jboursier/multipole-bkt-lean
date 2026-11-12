/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Energy.RouteNeumann.Base

/-!
# The displayed Neumann Green kernel

Equation (3.19) of the paper uses the logarithmic pole, its image logarithm,
and the quadratic compensator. The image logarithm is defined directly at a
centered source. No image point at infinity is needed.
-/

@[expose] public section

open MeasureTheory Metric Set InnerProductSpace ComplexConjugate
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT.RouteGreen

/-- The displayed unit-disc kernel (3.19).
The logarithm has the usual Mathlib value on its singular set. The source
equation is distributional and never uses a pointwise value at the pole. -/
noncomputable def kernel (x y : ℂ) : ℝ :=
  -Real.log ‖x - y‖ - Real.log ‖1 - x * conj y‖ + ‖x‖ ^ 2 / 2

/-- The gradient of the displayed kernel away from its logarithmic poles.
The three terms follow the order in (3.19). -/
noncomputable def field (x y : ℂ) : ℂ :=
  -((‖x - y‖ ^ 2)⁻¹ : ℝ) • (x - y) + screenedImageField 0 1 y x + x

/-- The quadratic term is the compensator for the constant source density in the
Green problem preceding (3.19). -/
noncomputable def compensator (x : ℂ) : ℝ := ‖x‖ ^ 2 / 2

/-- The compensating probability density in the Green problem preceding (3.19). -/
noncomputable def density : ℝ := Real.pi⁻¹

/-- The centered-source formula is obtained directly, equation (3.19). -/
theorem kernel_center (x : ℂ) : kernel x 0 = -Real.log ‖x‖ + ‖x‖ ^ 2 / 2 := by
  simp [kernel]

/-- The centered image field vanishes, including at the pole, (3.19). -/
theorem field_center (x : ℂ) :
    field x 0 = -((‖x‖ ^ 2)⁻¹ : ℝ) • x + x := by
  simp [field, screenedImageField]

/-- The image logarithm in (3.19) is the existing image potential,
with unit radius and zero center. -/
theorem kernel_decomposition (x y : ℂ) :
    kernel x y = logKernel (x - y) + screenedImagePotential 0 1 y x + compensator x := by
  simp [kernel, logKernel, screenedImagePotential, compensator, sub_eq_add_neg]

/-- The image logarithm has no singularity on the closed unit disc when the
source is in the open unit disc, equation (3.19). -/
theorem image_arg_ne_zero {x y : ℂ} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ < 1) :
    1 - x * conj y ≠ 0 := by
  have h : ‖x - 0‖ * ‖y - 0‖ < (1 : ℝ) ^ 2 := by
    simp only [sub_zero, one_pow]
    exact (mul_le_mul_of_nonneg_right hx (norm_nonneg y)).trans_lt (by simpa using hy)
  simpa using screenedImagePotential_arg_ne_zero h

/-- Derivative of the compensator. Its gradient is `x`, equation (3.19). -/
theorem hasFDerivAt_compensator (x : ℂ) :
    HasFDerivAt compensator (toDual ℝ ℂ x) x := by
  have h := ((hasFDerivAt_id x).norm_sq).const_mul (1 / 2 : ℝ)
  convert h using 1
  · funext w
    simp [compensator, div_eq_mul_inv, mul_comm]
  · ext v
    simp [toDual_apply_apply, innerSL_apply_apply]
    ring

/-- Differentiating the three displayed terms, equation (3.19).
Only the actual pole is excluded on the closed unit disc. -/
theorem hasFDerivAt_kernel {x y : ℂ} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ < 1)
    (hxy : x ≠ y) : HasFDerivAt (fun w => kernel w y) (toDual ℝ ℂ (field x y)) x := by
  have hp := (hasFDerivAt_neg_log_norm (sub_ne_zero.2 hxy)).comp x
    ((hasFDerivAt_id x).sub_const y)
  have hi := hasFDerivAt_screenedImagePotential (z := 0) (τ := 1)
    (by simpa using image_arg_ne_zero hx hy)
  have h := (hp.add hi).add (hasFDerivAt_compensator x)
  simp only [ContinuousLinearMap.comp_id] at h
  convert h using 1
  · funext w
    exact kernel_decomposition w y
  · simp only [field, map_add]

/-- The normal component of the logarithmic pole and image is `-1`,
the display after (3.19), including a centered source. -/
theorem logarithmic_boundary {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ < 1) :
    inner ℝ x (-((‖x - y‖ ^ 2)⁻¹ : ℝ) • (x - y) +
      screenedImageField 0 1 y x) = -1 := by
  simpa using inner_sub_add_screenedImageField_eq (z := 0) (τ := 1)
    (by simpa using hx) zero_lt_one (by simpa using hy)

/-- The quadratic compensator cancels the normal derivative `-1`,
as in the display after (3.19). The outward unit normal is `x`. -/
theorem boundary {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ < 1) :
    inner ℝ x (field x y) = 0 := by
  rw [field, inner_add_right, logarithmic_boundary hx hy, real_inner_self_eq_norm_sq, hx]
  norm_num

/-- The Neumann boundary identity for the derivative of the displayed
potential itself, as in the display after (3.19). -/
theorem normal_derivative {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ < 1) :
    fderiv ℝ (fun w => kernel w y) x x = 0 := by
  have hxy : x ≠ y := by
    intro h
    rw [← h, hx] at hy
    exact (lt_irrefl 1 hy)
  rw [(hasFDerivAt_kernel hx.le hy hxy).fderiv, toDual_apply_apply,
    real_inner_comm, boundary hx hy]

end MultipoleBKT.RouteGreen
