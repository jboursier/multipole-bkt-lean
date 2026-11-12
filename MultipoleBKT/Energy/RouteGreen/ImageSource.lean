/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Energy.RouteNeumann.Base
public import TwoComponentCoulomb.Potential.Fundamental

/-!
# Testing the image pole

The image pole lies outside the disc in (3.19).
These fundamental-solution identities precede the Green source equation.
-/

public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace ComplexConjugate

namespace MultipoleBKT

/-- The image field tested against `∇ξ` is integrable (`ξ` of class `C¹` with compact support). -/
theorem integrable_fderiv_apply_screenedImageField {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ)
    (hc : HasCompactSupport ξ) (z : ℂ) (τ : ℝ) (a : ℂ) :
    Integrable fun w => fderiv ℝ ξ w (screenedImageField z τ a w) := by
  by_cases ha : a = z
  · have : (fun w => fderiv ℝ ξ w (screenedImageField z τ a w)) = fun _ => 0 := by
      funext w
      simp [screenedImageField, ha]
    rw [this]
    exact integrable_zero _ _ _
  · simp_rw [screenedImageField_eq_of_ne τ ha]
    set p := imagePoint z τ a
    have hη : ContDiff ℝ 1 fun u => ξ (p + u) := hξ.comp (contDiff_const.add contDiff_id)
    have hηc : HasCompactSupport fun u => ξ (p + u) :=
      hc.comp_isClosedEmbedding (Homeomorph.addLeft p).isClosedEmbedding
    have h0 :=
      (TwoComponentCoulomb.integrable_fderiv_apply_gradLogKernel_zero hη hηc).comp_sub_right p
    refine h0.congr (Eventually.of_forall fun w => ?_)
    simp only
    rw [TwoComponentCoulomb.fderiv_apply_gradLogKernel_translate p w]

/-- The image field tested against `∇ξ` integrates to `2π ξ(a*) = 0` when `ξ` vanishes at the
image point (Green's identity for a point charge, `integral_fderiv_apply_gradLogKernel`). -/
theorem integral_fderiv_apply_screenedImageField {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ)
    (hc : HasCompactSupport ξ) (z : ℂ) (τ : ℝ) (a : ℂ) (h : a ≠ z → ξ (imagePoint z τ a) = 0) :
    ∫ w, fderiv ℝ ξ w (screenedImageField z τ a w) = 0 := by
  by_cases ha : a = z
  · simp [screenedImageField, ha]
  · simp_rw [screenedImageField_eq_of_ne τ ha]
    rw [TwoComponentCoulomb.integral_fderiv_apply_gradLogKernel hξ hc, h ha, mul_zero]

end MultipoleBKT
