/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.RouteFlux.Field
public import MultipoleBKT.Potential.TwoRadius
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TwoComponentCoulomb.Potential.DiscField

/-!
# First derivatives of the potential from the convolution field

See Lemma 3.1 of the paper. Integrating the point field along real segments and using Fubini
identifies the radial derivative of the potential with the continuous convolution
field. The flux formula then gives minus enclosed mass divided by radius.

This argument does not differentiate the logarithmic Newton formula.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped ENNReal RealInnerProductSpace
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT.RouteFlux

variable {χ : ℂ → ℝ} {α : ℝ}

private theorem ae_im_ne_zero (χ : ℂ → ℝ) (α : ℝ) :
    ∀ᵐ y ∂smearedCharge χ 0 α, y.im ≠ 0 := by
  let s : Submodule ℝ ℂ := LinearMap.ker Complex.imCLM.toLinearMap
  have hs : s ≠ ⊤ := by
    intro hs
    have hi : Complex.I ∈ s := by rw [hs]; trivial
    simp [s, LinearMap.mem_ker] at hi
  have h := smearedCharge_absolutelyContinuous χ 0 α (Measure.addHaar_submodule volume s hs)
  rw [ae_iff]
  convert h using 2
  ext y
  simp [s, LinearMap.mem_ker]

private theorem real_sub_ne_zero {y : ℂ} (hy : y.im ≠ 0) (t : ℝ) : (t : ℂ) - y ≠ 0 := by
  intro h
  have hi := congrArg Complex.im (sub_eq_zero.mp h)
  simp only [Complex.ofReal_im] at hi
  exact hy hi.symm

private theorem point_real_hasDerivAt {y : ℂ} (hy : y.im ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => logKernel ((s : ℂ) - y))
      ⟪pointField ((t : ℂ) - y), (1 : ℂ)⟫ t := by
  have h := (hasFDerivAt_neg_log_norm (real_sub_ne_zero hy t)).comp_hasDerivAt t
    (((hasDerivAt_id t).ofReal_comp).sub_const y)
  simpa only [logKernel, pointField, toDual_apply_apply, Function.comp_def, id_eq, Complex.ofReal_one] using h

private theorem continuous_point_real {y : ℂ} (hy : y.im ≠ 0) :
    Continuous (fun t : ℝ => ⟪pointField ((t : ℂ) - y), (1 : ℂ)⟫) := by
  have hc : Continuous (fun t : ℝ => (t : ℂ) - y) := Complex.continuous_ofReal.sub continuous_const
  have hf : Continuous (fun t : ℝ => pointField ((t : ℂ) - y)) :=
    ((((hc.norm).pow 2).inv₀ (fun t => pow_ne_zero 2
      (norm_ne_zero_iff.mpr (real_sub_ne_zero hy t)))).neg).smul hc
  exact hf.inner continuous_const

private theorem point_real_sub_eq_integral {y : ℂ} (hy : y.im ≠ 0) (a b : ℝ) :
    logKernel ((b : ℂ) - y) - logKernel ((a : ℂ) - y) =
      ∫ t in a..b, ⟪pointField ((t : ℂ) - y), (1 : ℂ)⟫ := by
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => point_real_hasDerivAt hy t) ((continuous_point_real hy).intervalIntegrable a b)).symm

private theorem integrable_real_prod (hχ : IsMollifier χ) (hα : 0 < α) (a b : ℝ) :
    Integrable (fun p : ℝ × ℂ => ⟪pointField ((p.1 : ℂ) - p.2), (1 : ℂ)⟫)
      ((volume.restrict (Ioc a b)).prod (smearedCharge χ 0 α)) := by
  have := isFiniteMeasure_smearedCharge hχ 0 α
  have hc : Continuous (fun p : ℝ × ℂ => (p.1 : ℂ) - p.2) :=
    (Complex.continuous_ofReal.comp continuous_fst).sub continuous_snd
  have hm : Measurable (fun p : ℝ × ℂ => pointField ((p.1 : ℂ) - p.2)) :=
    TwoComponentCoulomb.measurable_gradLogKernel.comp hc.measurable
  have hi : Integrable (fun p : ℝ × ℂ => pointField ((p.1 : ℂ) - p.2))
      ((volume.restrict (Ioc a b)).prod (smearedCharge χ 0 α)) := by
    apply (integrable_prod_iff (μ := volume.restrict (Ioc a b))
      (ν := smearedCharge χ 0 α) hm.aestronglyMeasurable).mpr
    refine ⟨?_, ?_⟩
    · exact Eventually.of_forall (fun t : ℝ =>
        integrable_gradLogKernel_sub_smearedCharge hχ (t : ℂ) 0 hα)
    · obtain ⟨C, hC⟩ := exists_integral_norm_pointField_le hχ 0 hα (|a| + |b| + 1)
      apply (integrable_const C).mono' hm.aestronglyMeasurable.norm.integral_prod_right'
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      apply hC
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      have : |t| ≤ max |a| |b| := abs_le_max_abs_abs ht.1.le ht.2
      have : |t| ≤ |a| + |b| := this.trans (max_le_add_of_nonneg (abs_nonneg _) (abs_nonneg _))
      linarith
  exact (((innerSL ℝ).flip (1 : ℂ)).integrable_comp hi)

/-- The fundamental theorem along a real segment for the actual convolved potential.
The exceptional source points on the real axis form a null set. -/
theorem smearedPotential_sub_eq_integral_field (hχ : IsMollifier χ) (hα : 0 < α) (a b : ℝ) :
    smearedPotential χ α (b : ℂ) - smearedPotential χ α (a : ℂ) =
      ∫ t in a..b, ⟪convolvedField χ 0 α (t : ℂ), (1 : ℂ)⟫ := by
  wlog hab : a ≤ b generalizing a b
  · have h := this b a (le_of_not_ge hab)
    rw [intervalIntegral.integral_symm]
    linarith
  have hprod := integrable_real_prod hχ hα a b
  have he : ∀ t : ℝ, ⟪convolvedField χ 0 α (t : ℂ), (1 : ℂ)⟫ =
      ∫ y, ⟪pointField ((t : ℂ) - y), (1 : ℂ)⟫ ∂smearedCharge χ 0 α := fun t =>
    (((innerSL ℝ).flip (1 : ℂ)).integral_comp_comm
      (integrable_gradLogKernel_sub_smearedCharge hχ (t : ℂ) 0 hα)).symm
  have hint (t : ℝ) : Integrable (fun y => logKernel ((t : ℂ) - y)) (smearedCharge χ 0 α) :=
    (integrable_log_norm_sub_smearedCharge hχ (t : ℂ) 0 α).neg
  rw [smearedPotential, smearedPotential, ← integral_sub (hint b) (hint a)]
  rw [integral_congr_ae ((ae_im_ne_zero χ α).mono fun y hy => point_real_sub_eq_integral hy a b)]
  simp_rw [intervalIntegral.integral_of_le hab]
  rw [← integral_integral_swap hprod]
  simp_rw [he]

/-- The radial derivative of the potential is the convolved point field.
Its continuity follows from the locally integrable fundamental-solution route. -/
theorem hasDerivAt_smearedPotential_real (hχ : IsMollifier χ) (hα : 0 < α) (r : ℝ) :
    HasDerivAt (fun t : ℝ => smearedPotential χ α (t : ℂ))
      ⟪convolvedField χ 0 α (r : ℂ), (1 : ℂ)⟫ r := by
  have hc : Continuous (fun t : ℝ => ⟪convolvedField χ 0 α (t : ℂ), (1 : ℂ)⟫) :=
    ((continuous_convolvedField hχ hα).comp Complex.continuous_ofReal).inner continuous_const
  have he : (fun t : ℝ => smearedPotential χ α (t : ℂ)) =
      fun t => smearedPotential χ α 0 +
        ∫ s in (0 : ℝ)..t, ⟪convolvedField χ 0 α (s : ℂ), (1 : ℂ)⟫ := by
    funext t
    have h := smearedPotential_sub_eq_integral_field hχ hα 0 t
    simpa using (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 r)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add _

/-- The paper's radial derivative identity, derived from the Poisson flux. -/
theorem hasDerivAt_smearedPotential_radial (hχ : IsMollifier χ) (hα : 0 < α)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t : ℝ => smearedPotential χ α (t : ℂ)) (-massProfile χ α r / r) r := by
  simpa only [radialComponent_convolvedField hχ hα hr] using
    hasDerivAt_smearedPotential_real hχ hα r

private theorem norm_hasFDerivAt {x : ℂ} (hx : x ≠ 0) :
    HasFDerivAt (fun y : ℂ => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hr.ne')
  simp only [Real.sqrt_sq (norm_nonneg _)] at h
  apply h.congr_fderiv
  ext v
  simp only [smul_apply, smul_eq_mul, nsmul_eq_mul]
  field_simp
  norm_num

/-- First differentiability of the actual singly smoothed potential, obtained from
the flux field and real-segment integration. At zero, the zero radial derivative
composes with the norm by its little-o estimate. -/
theorem hasFDerivAt_smearedPotential (hχ : IsMollifier χ) (hα : 0 < α) (x : ℂ) :
    HasFDerivAt (smearedPotential χ α) (toDual ℝ ℂ (convolvedField χ 0 α x)) x := by
  have he (y : ℂ) : smearedPotential χ α y = smearedPotential χ α (‖y‖ : ℂ) :=
    smearedPotential_eq_of_norm_eq hχ hα (by simp)
  by_cases hx : x = 0
  · subst x
    have hzero : convolvedField χ 0 α 0 = 0 := by
      rw [convolvedField_eq_massProfile hχ hα]
      simp
    rw [hzero, map_zero, hasFDerivAt_iff_isLittleO_nhds_zero]
    have h := (hasDerivAt_smearedPotential_real hχ hα 0).isLittleO
    simp only [Complex.ofReal_zero, hzero, inner_zero_left, smul_zero, sub_zero] at h
    have hcomp := h.comp_tendsto (show Tendsto (fun y : ℂ => ‖y‖) (𝓝 0) (𝓝 0) by
      simpa only [norm_zero] using continuous_norm.tendsto (0 : ℂ))
    have hb : (fun y : ℂ => ‖y‖) =O[𝓝 (0 : ℂ)] (fun y : ℂ => y) := by
      exact Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun y => by simp)
    have hs : (fun y : ℂ => smearedPotential χ α (‖y‖ : ℂ) - smearedPotential χ α 0)
        =o[𝓝 0] (fun y : ℂ => y) := by
      simpa only [Function.comp_def] using hcomp.trans_isBigO hb
    convert hs using 1
    ext y
    simp only [zero_add, zero_apply, sub_zero]
    rw [he y]
  · have hr := norm_pos_iff.mpr hx
    have h := (hasDerivAt_smearedPotential_radial hχ hα hr).comp_hasFDerivAt x
      (norm_hasFDerivAt hx)
    have hf : (fun y : ℂ => smearedPotential χ α (‖y‖ : ℂ)) = smearedPotential χ α :=
      funext fun y => (he y).symm
    simp only [Function.comp_def] at h
    rw [hf] at h
    apply h.congr_fderiv
    ext v
    rw [convolvedField_eq_massProfile hχ hα]
    simp only [smul_apply, smul_eq_mul, innerSL_apply_apply,
      toDual_apply_apply, real_inner_smul_left]
    field_simp

/-- Identification of the classical gradient with the field recovered from flux. -/
theorem hasGradientAt_smearedPotential (hχ : IsMollifier χ) (hα : 0 < α) (x : ℂ) :
    HasGradientAt (smearedPotential χ α) (convolvedField χ 0 α x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact hasFDerivAt_smearedPotential hχ hα x

/-- Continuity of the gradient for the actual bounded measurable mollifier assumptions. -/
theorem continuous_gradient_smearedPotential (hχ : IsMollifier χ) (hα : 0 < α) :
    Continuous (gradient (smearedPotential χ α)) := by
  have he : gradient (smearedPotential χ α) = convolvedField χ 0 α :=
    funext fun x => (hasGradientAt_smearedPotential hχ hα x).gradient
  rw [he]
  exact continuous_convolvedField hχ hα

/-- The weak Poisson equation for the actual potential, available below Regularity
and Electric. The right hand side has only a bounded measurable density. -/
theorem weakPoisson_smearedPotential (hχ : IsMollifier χ) {ξ : ℂ → ℝ}
    (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ) (hα : 0 < α) :
    ∫ x, fderiv ℝ ξ x (gradient (smearedPotential χ α) x) =
      2 * Real.pi * ∫ y, ξ y ∂smearedCharge χ 0 α := by
  simp_rw [(hasGradientAt_smearedPotential hχ hα _).gradient]
  exact weakPoisson_convolvedField hχ hξ hc 0 hα

end MultipoleBKT.RouteFlux

end
