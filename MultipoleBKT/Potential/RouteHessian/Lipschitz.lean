/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.RouteHessian.WeakConvolution
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A bounded weak Hessian gives a globally Lipschitz field

See Lemma 3.1 of the paper. Smooth the weak identity, apply the mean value theorem with the
same tensor bound, and let the smoothing radius tend to zero.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace ContinuousLinearMap
open scoped RealInnerProductSpace Convolution

namespace MultipoleBKT.RouteHessian

/-- A fixed approximate identity with positive radii decreasing to zero. -/
noncomputable def shrinkingBump (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := (1 / ((n : ℝ) + 1)) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- The radii of the approximate identity tend to zero. -/
theorem tendsto_shrinkingBump :
    Tendsto (fun n => (shrinkingBump n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Convolution preserves an operator bound, multiplied by the kernel's `L¹` norm. -/
theorem norm_convolution_le_of_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {φ : ℂ → ℝ} {G : ℂ → E} (hφ : Integrable φ)
    {K : ℝ} (hK : ∀ x, ‖G x‖ ≤ K) (z : ℂ) :
    ‖(φ ⋆[lsmul ℝ ℝ] G) z‖ ≤ (∫ t, ‖φ t‖) * K := by
  change ‖∫ t, φ t • G (z - t)‖ ≤ _
  calc
    _ ≤ ∫ t, ‖φ t‖ * K := norm_integral_le_of_norm_le (hφ.norm.mul_const K)
      (Eventually.of_forall fun t => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hK _) (norm_nonneg _))
    _ = _ := integral_mul_const _ _

/-- The normed smoothings preserve the bound exactly. -/
theorem norm_bump_convolution_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (φ : ContDiffBump (0 : ℂ)) {G : ℂ → E}
    {K : ℝ} (hK : ∀ x, ‖G x‖ ≤ K) (z : ℂ) :
    ‖(φ.normed volume ⋆[lsmul ℝ ℝ] G) z‖ ≤ K := by
  have h := norm_convolution_le_of_bound (φ.integrable_normed (μ := volume)) hK z
  simp_rw [Real.norm_of_nonneg (φ.nonneg_normed _), φ.integral_normed, one_mul] at h
  exact h

/-- Internal weak-derivative bridge: a continuous field with bounded weak derivative
is globally Lipschitz. Smooth tests suffice, without any regularity of the tensor. -/
theorem norm_sub_le_of_weakDerivative {F : ℂ → ℂ} {H : ℂ → ℂ →L[ℝ] ℂ}
    (hF : Continuous F) (hH : Measurable H) {K : ℝ} (hK : ∀ x, ‖H x‖ ≤ K)
    (hweak : ∀ (ξ : ℂ → ℝ), ContDiff ℝ 1 ξ → HasCompactSupport ξ → ∀ v w : ℂ,
      (∫ y, fderiv ℝ ξ y v * ⟪F y, w⟫) = -(∫ y, ξ y * ⟪H y v, w⟫))
    (x y : ℂ) : ‖F x - F y‖ ≤ K * ‖x - y‖ := by
  have hd (n : ℕ) (z : ℂ) := hasFDerivAt_convolution_of_weak hF hH hK hweak
    ((shrinkingBump n).contDiff_normed (μ := volume))
    ((shrinkingBump n).hasCompactSupport_normed (μ := volume)) z
  have hbound (n : ℕ) (z : ℂ) := norm_bump_convolution_le (shrinkingBump n) hK z
  have hL (n : ℕ) :
      ‖((shrinkingBump n).normed volume ⋆[lsmul ℝ ℝ] F) x -
        ((shrinkingBump n).normed volume ⋆[lsmul ℝ ℝ] F) y‖ ≤ K * ‖x - y‖ :=
    (convex_univ : Convex ℝ (univ : Set ℂ)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z _ => (hd n z).hasFDerivWithinAt) (fun z _ => hbound n z) (mem_univ y) (mem_univ x)
  have ht (z : ℂ) := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) tendsto_shrinkingBump hF z
  exact le_of_tendsto ((ht x).sub (ht y)).norm (Eventually.of_forall hL)

/-- The field is globally Lipschitz by its identified bounded weak Hessian.
The paper: Lemma 3.1. -/
theorem norm_convolvedField_sub_le {χ : ℂ → ℝ} {lam : ℝ} (hχ : IsMollifier χ) {M : ℝ}
    (hM : ∀ x, χ x ≤ M) (hlam : 0 < lam) (x y : ℂ) :
    ‖RouteFlux.convolvedField χ 0 lam x - RouteFlux.convolvedField χ 0 lam y‖ ≤
      3 * (Real.pi * M / lam ^ 2) * ‖x - y‖ :=
  norm_sub_le_of_weakDerivative (RouteFlux.continuous_convolvedField hχ hlam)
    (measurable_radialHessian hχ) (norm_radialHessian_le hχ hM hlam)
    (fun _ hξ hc v w => weakHessian_convolvedField hχ hlam hξ hc v w) x y

end MultipoleBKT.RouteHessian

end
