/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Energy.RouteGreen.Source
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.IntegrableOn
import TwoComponentCoulomb.Potential.DiscField
import TwoComponentCoulomb.Potential.DiscPotential

/-!
# The weak derivative at the logarithmic pole

In (3.19), the point source is interpreted distributionally.
This file verifies that `field` is the weak gradient of `kernel`, including
across the pole. Integration by parts on almost every coordinate line avoids
the pole. Fubini's theorem then gives the identity in the disc.
-/

@[expose] public section

open MeasureTheory Metric Set InnerProductSpace Filter

namespace MultipoleBKT.RouteGreen

/-- The displayed potential is integrable on the unit disc, equation (3.19), including its logarithmic pole. -/
theorem integrableOn_kernel {y : ℂ} (hy : ‖y‖ < 1) :
    IntegrableOn (fun x => kernel x y) (ball 0 1) := by
  have hp : IntegrableOn (fun x : ℂ => -Real.log ‖x - y‖) (ball 0 1) := by
    apply ((TwoComponentCoulomb.integrableOn_log_norm_sub_ball y 0 1).neg).congr_fun
      (fun x _ => by simp [norm_sub_rev]) measurableSet_ball
  have hi : ContinuousOn (screenedImagePotential 0 1 y) (closedBall 0 1) := by
    intro x hx
    apply (contDiffAt_screenedImagePotential (z := 0) (τ := 1)
      (by simpa using image_arg_ne_zero (by simpa using hx) hy)).continuousAt.continuousWithinAt
  have hq : Continuous compensator := by
    unfold compensator
    fun_prop
  have hadd := (hp.add ((hi.integrableOn_compact (isCompact_closedBall 0 1)).mono_set
    ball_subset_closedBall)).add ((hq.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)).mono_set
      ball_subset_closedBall)
  exact hadd.congr_fun (fun x _ => (kernel_decomposition x y).symm) measurableSet_ball

/-- The displayed gradient is integrable on the unit disc, equation (3.19). Its singularity is bounded by `1/|x-y|`. -/
theorem integrableOn_field {y : ℂ} (hy : ‖y‖ < 1) :
    IntegrableOn (fun x => field x y) (ball 0 1) := by
  have hp := TwoComponentCoulomb.integrableOn_comp_sub_ball
    TwoComponentCoulomb.integrableOn_gradLogKernel_ball_zero y 0 1
  have hp' : IntegrableOn (fun x : ℂ => -((‖x - y‖ ^ 2)⁻¹ : ℝ) • (x - y))
      (ball 0 1) := by
    convert hp.neg using 1
    funext x
    simp only [Pi.neg_apply]
    rw [norm_sub_rev, ← neg_sub y x, smul_neg]
  have hi : ContinuousOn (screenedImageField 0 1 y) (closedBall 0 1) := by
    intro x hx
    apply (continuousAt_screenedImageField ?_).continuousWithinAt
    apply screenedImage_denom_ne_zero
    simp only [sub_zero, one_pow]
    have hx' : ‖x‖ ≤ 1 := by simpa using hx
    exact (mul_le_mul_of_nonneg_right hx' (norm_nonneg y)).trans_lt (by simpa using hy)
  exact (hp'.add ((hi.integrableOn_compact (isCompact_closedBall 0 1)).mono_set
    ball_subset_closedBall)).add ((continuous_id.continuousOn.integrableOn_compact
      (isCompact_closedBall 0 1)).mono_set ball_subset_closedBall)

private theorem integrable_test_mul {f ξ : ℂ → ℝ}
    (hf : IntegrableOn f (ball 0 1)) (hξ : Continuous ξ) (hc : HasCompactSupport ξ)
    (hs : tsupport ξ ⊆ ball 0 1) : Integrable fun x => f x * ξ x := by
  obtain ⟨C, hC⟩ := hξ.bounded_above_of_compact_support hc
  have h := hf.mul_bdd hξ.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  apply IntegrableOn.integrable_of_forall_notMem_eq_zero h
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun hmem => hx (hs hmem)), mul_zero]

private theorem integral_coordinate_parts {f ξ : ℂ → ℝ} {F : ℂ → ℂ}
    (L : (ℝ × ℝ) ≃L[ℝ] ℂ) (hL : MeasurePreserving L (volume.prod volume) volume)
    (y : ℂ) (hξ : ContDiff ℝ 1 ξ)
    (hf : ∀ x ∈ tsupport ξ, x ≠ y → HasFDerivAt f (toDual ℝ ℂ (F x)) x)
    (hfg : Integrable fun x => f x * ξ x)
    (hfg' : Integrable fun x => f x * fderiv ℝ ξ x (L (0, 1)))
    (hf'g : Integrable fun x => inner ℝ (F x) (L (0, 1)) * ξ x) :
    ∫ x, f x * fderiv ℝ ξ x (L (0, 1)) =
      -∫ x, inner ℝ (F x) (L (0, 1)) * ξ x := by
  have he := L.toHomeomorph.measurableEmbedding
  have hfgL := (hL.integrable_comp_emb he).2 hfg
  have hfg'L := (hL.integrable_comp_emb he).2 hfg'
  have hf'gL := (hL.integrable_comp_emb he).2 hf'g
  simp only [Function.comp_def] at hfgL hfg'L hf'gL
  rw [← hL.integral_comp he (fun x => f x * fderiv ℝ ξ x (L (0, 1))),
    ← hL.integral_comp he (fun x => inner ℝ (F x) (L (0, 1)) * ξ x),
    integral_prod _ hfg'L, integral_prod _ hf'gL, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hfgL.prod_right_ae, hfg'L.prod_right_ae, hf'gL.prod_right_ae,
    volume.ae_ne (L.symm y).1] with s h0 h1 h2 hs
  have hn (t : ℝ) : L (s, t) ≠ y := by
    intro h
    have := congrArg (fun x => (L.symm x).1) h
    exact hs (by simpa using this)
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => L (s, t)) (L (0, 1)) t := by
    exact L.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))
  apply integral_mul_deriv_eq_deriv_mul_of_integrable
  · intro t ht
    have hmem : L (s, t) ∈ tsupport ξ :=
      tsupport_comp_subset_preimage (f := fun t : ℝ => L (s, t)) ξ (by fun_prop) ht
    exact (hf _ hmem (hn t)).comp_hasDerivAt t (hd t)
  · intro t _
    exact (hξ.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t (hd t)
  · exact h1
  · exact h2
  · exact h0

private theorem integrable_field_component_test {y : ℂ} (hy : ‖y‖ < 1)
    {ξ : ℂ → ℝ} (hξ : Continuous ξ) (hc : HasCompactSupport ξ)
    (hs : tsupport ξ ⊆ ball 0 1) (v : ℂ) :
    Integrable fun x => inner ℝ (field x y) v * ξ x := by
  have hi := (innerSL ℝ v).integrable_comp (integrableOn_field hy)
  have hi' : IntegrableOn (fun x => inner ℝ (field x y) v) (ball 0 1) :=
    IntegrableOn.congr_fun hi (fun x _ => by
      simp only [innerSL_apply_apply]
      exact real_inner_comm _ _) measurableSet_ball
  exact integrable_test_mul hi' hξ hc hs

/-- `field` is the weak gradient of the displayed `kernel` across the
logarithmic pole, equation (3.19).
For every direction `v`, `∫ G ∂ᵥξ = -∫ ξ ∇G·v`. -/
theorem weak_derivative {y : ℂ} (hy : ‖y‖ < 1) {ξ : ℂ → ℝ}
    (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ)
    (hs : tsupport ξ ⊆ ball 0 1) (v : ℂ) :
    ∫ x, kernel x y * fderiv ℝ ξ x v =
      -∫ x, inner ℝ (field x y) v * ξ x := by
  have hfg := integrable_test_mul (integrableOn_kernel hy) hξ.continuous hc hs
  have hfg' (u : ℂ) : Integrable fun x => kernel x y * fderiv ℝ ξ x u :=
    integrable_test_mul (integrableOn_kernel hy)
      ((hξ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (hc.fderiv_apply ℝ u) ((tsupport_fderiv_apply_subset (f := ξ) ℝ u).trans hs)
  have hf'g := integrable_field_component_test hy hξ.continuous hc hs
  have hf (x : ℂ) (hx : x ∈ tsupport ξ) (hxy : x ≠ y) :
      HasFDerivAt (fun w => kernel w y) (toDual ℝ ℂ (field x y)) x :=
    hasFDerivAt_kernel (by have h := hs hx; rw [mem_ball_zero_iff] at h; exact h.le) hy hxy
  let L₁ : (ℝ × ℝ) ≃L[ℝ] ℂ :=
    (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).trans Complex.equivRealProdCLM.symm
  let L₂ := Complex.equivRealProdCLM.symm
  have hm₂ : MeasurePreserving L₂ (volume.prod volume) volume :=
    Complex.volume_preserving_equiv_real_prod.symm
  have hm₁ : MeasurePreserving L₁ (volume.prod volume) volume :=
    hm₂.comp Measure.measurePreserving_swap
  have h₁ := integral_coordinate_parts L₁ hm₁ y hξ hf hfg (hfg' _) (hf'g _)
  have h₂ := integral_coordinate_parts L₂ hm₂ y hξ hf hfg (hfg' _) (hf'g _)
  change (∫ x, kernel x y * fderiv ℝ ξ x 1) =
    -∫ x, inner ℝ (field x y) 1 * ξ x at h₁
  change (∫ x, kernel x y * fderiv ℝ ξ x Complex.I) =
    -∫ x, inner ℝ (field x y) Complex.I * ξ x at h₂
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im v).symm
  conv_lhs => arg 2; ext x; rw [hv, map_add, map_smul, map_smul]
  conv_rhs => arg 1; arg 2; ext x; rw [hv, inner_add_right,
    real_inner_smul_right, real_inner_smul_right]
  simp only [smul_eq_mul, mul_add, add_mul]
  simp_rw [show ∀ x : ℂ, kernel x y * (v.re * fderiv ℝ ξ x 1) =
      v.re * (kernel x y * fderiv ℝ ξ x 1) by intro x; ring,
    show ∀ x : ℂ, kernel x y * (v.im * fderiv ℝ ξ x Complex.I) =
      v.im * (kernel x y * fderiv ℝ ξ x Complex.I) by intro x; ring,
    mul_assoc]
  rw [integral_add ((hfg' 1).const_mul _) ((hfg' Complex.I).const_mul _),
    integral_add ((hf'g 1).const_mul _) ((hf'g Complex.I).const_mul _)]
  simp only [integral_const_mul, h₁, h₂]
  ring

private theorem laplacian_coordinates {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 2 ξ) (x : ℂ) :
    Laplacian.laplacian ξ x =
      fderiv ℝ (fun w => fderiv ℝ ξ w 1) x 1 +
      fderiv ℝ (fun w => fderiv ℝ ξ w Complex.I) x Complex.I := by
  have hd (v : ℂ) : fderiv ℝ (fun w => fderiv ℝ ξ w v) x v =
      fderiv ℝ (fderiv ℝ ξ) x v v := by
    rw [fderiv_clm_apply ((hξ.fderiv_right (by norm_num)).differentiable one_ne_zero x)
      (differentiableAt_const v)]
    simp
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hd]

/-- The source equation of the Green problem preceding (3.19), for the potential itself. In the distributional convention `⟨-ΔG,ξ⟩ = -∫ G Δξ`,
this states `-ΔG = 2π(δ_y - 1/π)` in the unit disc. Compactly supported
`C²` tests suffice and include all smooth test functions. -/
theorem distributional_source {y : ℂ} (hy : ‖y‖ < 1) {ξ : ℂ → ℝ}
    (hξ : ContDiff ℝ 2 ξ) (hc : HasCompactSupport ξ)
    (hs : tsupport ξ ⊆ ball 0 1) :
    -(∫ x, kernel x y * Laplacian.laplacian ξ x) =
      2 * Real.pi * (ξ y - ∫ x, density * ξ x) := by
  have hD (v : ℂ) : ContDiff ℝ 1 (fun x => fderiv ℝ ξ x v) :=
    (hξ.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hsD (v : ℂ) : tsupport (fun x => fderiv ℝ ξ x v) ⊆ ball 0 1 :=
    (tsupport_fderiv_apply_subset (f := ξ) ℝ v).trans hs
  have hi (v : ℂ) : Integrable fun x => kernel x y *
      fderiv ℝ (fun w => fderiv ℝ ξ w v) x v :=
    integrable_test_mul (integrableOn_kernel hy)
      (((hD v).continuous_fderiv one_ne_zero).clm_apply continuous_const)
      ((hc.fderiv_apply ℝ v).fderiv_apply ℝ v)
      ((tsupport_fderiv_apply_subset ℝ v).trans (hsD v))
  have hj (v : ℂ) : Integrable fun x => inner ℝ (field x y) v * fderiv ℝ ξ x v :=
    integrable_field_component_test hy (hD v).continuous (hc.fderiv_apply ℝ v) (hsD v) v
  have h₁ := weak_derivative hy (hD 1) (hc.fderiv_apply ℝ 1) (hsD 1) 1
  have h₂ := weak_derivative hy (hD Complex.I) (hc.fderiv_apply ℝ Complex.I)
    (hsD Complex.I) Complex.I
  have he (x : ℂ) : fderiv ℝ ξ x (field x y) =
      inner ℝ (field x y) 1 * fderiv ℝ ξ x 1 +
      inner ℝ (field x y) Complex.I * fderiv ℝ ξ x Complex.I := by
    have hv : field x y = (field x y).re • (1 : ℂ) + (field x y).im • Complex.I := by
      simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im (field x y)).symm
    calc fderiv ℝ ξ x (field x y) =
        fderiv ℝ ξ x ((field x y).re • (1 : ℂ) + (field x y).im • Complex.I) :=
          congrArg (fderiv ℝ ξ x) hv
      _ = _ := by rw [map_add, map_smul, map_smul]; simp
  simp_rw [laplacian_coordinates hξ, mul_add]
  rw [integral_add (hi 1) (hi Complex.I), h₁, h₂]
  have hsource := source hy (hξ.of_le (by norm_num)) hc hs
  simp_rw [he] at hsource
  rw [integral_add (hj 1) (hj Complex.I)] at hsource
  linarith

end MultipoleBKT.RouteGreen
