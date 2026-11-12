/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.RouteHessian.Weak
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Smoothing a bounded weak Hessian

See Lemma 3.1 of the paper. Testing the weak identity against a translated smooth kernel
identifies the derivative of the smoothed field with the smoothed tensor.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace ContinuousLinearMap
open scoped RealInnerProductSpace Convolution

namespace MultipoleBKT.RouteHessian

/-- A bounded measurable factor can be convolved against any integrable scalar kernel. -/
theorem integrable_smul_sub_of_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : ℂ → ℝ} {G : ℂ → E} (hφ : Integrable φ) (hG : AEStronglyMeasurable G volume)
    {K : ℝ} (hK : ∀ x, ‖G x‖ ≤ K) (z : ℂ) :
    Integrable (fun t => φ t • G (z - t)) := by
  exact hφ.smul_bdd K (hG.comp_measurePreserving (volume.measurePreserving_sub_left z))
    (Eventually.of_forall fun t => hK (z - t))

/-- Smooth convolution converts the weak derivative into a classical derivative.
This internal bridge is used with the radial weak Hessian and with its smoothings. -/
theorem hasFDerivAt_convolution_of_weak {F : ℂ → ℂ} {H : ℂ → ℂ →L[ℝ] ℂ}
    (hF : Continuous F) (hH : Measurable H) {K : ℝ} (hK : ∀ x, ‖H x‖ ≤ K)
    (hweak : ∀ (ξ : ℂ → ℝ), ContDiff ℝ 1 ξ → HasCompactSupport ξ → ∀ v w : ℂ,
      (∫ y, fderiv ℝ ξ y v * ⟪F y, w⟫) = -(∫ y, ξ y * ⟪H y v, w⟫))
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (z : ℂ) :
    HasFDerivAt (φ ⋆[lsmul ℝ ℝ] F) ((φ ⋆[lsmul ℝ ℝ] H) z) z := by
  have hd := hc.hasFDerivAt_convolution_left (lsmul ℝ ℝ) hφ (hF.locallyIntegrable (μ := volume)) z
  have hiD := ((hc.fderiv ℝ).convolutionExists_left ((lsmul ℝ ℝ).precompL ℂ)
    (hφ.continuous_fderiv one_ne_zero) (hF.locallyIntegrable (μ := volume)) z).integrable
  have hiH := integrable_smul_sub_of_bound
    (hφ.continuous.integrable_of_hasCompactSupport hc) hH.aestronglyMeasurable hK z
  have he : ((fderiv ℝ φ ⋆[(lsmul ℝ ℝ).precompL ℂ] F) z) =
      (φ ⋆[lsmul ℝ ℝ] H) z := by
    ext v
    apply ext_inner_right ℝ
    intro w
    let L : (ℂ →L[ℝ] ℂ) →L[ℝ] ℝ :=
      (innerSL ℝ w).comp (ContinuousLinearMap.apply ℝ ℂ v)
    have hiD' := L.integral_comp_comm hiD
    have hiH' := L.integral_comp_comm hiH
    simp only [L, ContinuousLinearMap.comp_apply, apply_apply,
      innerSL_apply_apply, precompL_apply, lsmul_apply, real_inner_smul_right] at hiD' hiH'
    simp_rw [real_inner_comm _ w] at hiD' hiH'
    change ⟪(∫ t, ((lsmul ℝ ℝ).precompL ℂ) (fderiv ℝ φ t) (F (z - t))) v, w⟫ =
      ⟪(∫ t, φ t • H (z - t)) v, w⟫
    rw [← hiD', ← hiH']
    let ξ : ℂ → ℝ := fun y => φ (z - y)
    have hξ : ContDiff ℝ 1 ξ := hφ.comp (contDiff_const.sub contDiff_id)
    have hξc : HasCompactSupport ξ := hc.comp_homeomorph (Homeomorph.subLeft z)
    have hξd (y v : ℂ) : fderiv ℝ ξ y v = -fderiv ℝ φ (z - y) v := by
      have hh := ((hφ.differentiable one_ne_zero) (z - y)).hasFDerivAt.comp y
        ((hasFDerivAt_const z y).sub (hasFDerivAt_id y))
      change fderiv ℝ (φ ∘ fun y : ℂ => z - y) y v = _
      rw [hh.fderiv]
      simp
    have hw := hweak ξ hξ hξc v w
    simp_rw [hξd, neg_mul, integral_neg] at hw
    have hh := neg_injective hw
    rw [← integral_sub_left_eq_self (fun t =>
      fderiv ℝ φ t v * ⟪F (z - t), w⟫) volume z]
    simp only [sub_sub_cancel]
    calc
      _ = ∫ y, ξ y * ⟪H y v, w⟫ := hh
      _ = ∫ t, φ t * ⟪H (z - t) v, w⟫ := by
        rw [← integral_sub_left_eq_self (fun t => φ t * ⟪H (z - t) v, w⟫) volume z]
        simp only [sub_sub_cancel, ξ]
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with t
        simp only [smul_apply, real_inner_smul_left]
  rw [he] at hd
  exact hd

end MultipoleBKT.RouteHessian

end
