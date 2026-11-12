/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.RouteHessian.ContinuousHessian

/-!
# The convolved Hessian tensor

See Lemma 3.1 of the paper. The Hessian of the double smoothing is the convolution of the radial
weak Hessian with the second charge. Its operator bound is preserved and it
is continuous for the paper's bounded measurable mollifier.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace ContinuousLinearMap
open scoped RealInnerProductSpace Convolution ENNReal

namespace MultipoleBKT

/-- The Euclidean Hessian tensor obtained by convolving the radial weak Hessian.
It is represented as the derivative of the gradient, using the Euclidean inner product. -/
noncomputable def twoRadiusHessian (χ : ℂ → ℝ) (α η : ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  ∫ a, RouteHessian.radialHessian χ η (z - a) ∂smearedCharge χ 0 α

namespace RouteHessian

variable {χ : ℂ → ℝ} {α η : ℝ}

/-- The scaled density has integral one, hence is integrable. -/
theorem integrable_chargeDensity (hχ : IsMollifier χ) (hα : 0 < α) :
    Integrable (RouteFlux.density χ α) := by
  have := isProbabilityMeasure_smearedCharge hχ 0 hα
  have he := integral_smearedCharge hχ 0 α (fun _ => (1 : ℝ))
  simp only [sub_zero, smul_eq_mul, mul_one] at he
  have hleft : (∫ a, (1 : ℝ) ∂smearedCharge χ 0 α) = 1 := by simp
  rw [hleft] at he
  exact Integrable.of_integral_ne_zero (by
    change (∫ a, (α ^ 2)⁻¹ * χ (a / (α : ℂ))) ≠ 0
    rw [← he]
    exact one_ne_zero)

/-- Integrating a translated function against the charge is convolution with its density. -/
theorem integral_charge_comp_sub_eq_convolution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hχ : IsMollifier χ) (α : ℝ) (G : ℂ → E) :
    (fun z => ∫ a, G (z - a) ∂smearedCharge χ 0 α) =
      RouteFlux.density χ α ⋆[lsmul ℝ ℝ] G := by
  ext z
  rw [integral_smearedCharge hχ]
  simp only [sub_zero, convolution_def, lsmul_apply, RouteFlux.density]

end RouteHessian

/-- The essential weak-Hessian bound survives convolution with the probability density. -/
theorem norm_twoRadiusHessian_le {χ : ℂ → ℝ} {α η M : ℝ} (hχ : IsMollifier χ)
    (hM : ∀ x, χ x ≤ M) (hα : 0 < α) (hη : 0 < η) (z : ℂ) :
    ‖twoRadiusHessian χ α η z‖ ≤ 3 * (Real.pi * M / η ^ 2) := by
  have := isProbabilityMeasure_smearedCharge hχ 0 hα
  have hh := norm_integral_le_of_norm_le_const (μ := smearedCharge χ 0 α)
    (Eventually.of_forall fun a => RouteHessian.norm_radialHessian_le hχ hM hη (z - a))
  simpa only [probReal_univ, mul_one, twoRadiusHessian] using hh

/-- The convolved weak Hessian is continuous, by `L¹` translation continuity. -/
theorem continuous_twoRadiusHessian {χ : ℂ → ℝ} {α η : ℝ}
    (hχ : IsMollifier χ) (hα : 0 < α) (hη : 0 < η) :
    Continuous (twoRadiusHessian χ α η) := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  change Continuous (fun z => ∫ a, RouteHessian.radialHessian χ η (z - a) ∂smearedCharge χ 0 α)
  rw [RouteHessian.integral_charge_comp_sub_eq_convolution hχ]
  exact (RouteHessian.uniformContinuous_convolution_of_integrable_bounded
    (RouteHessian.integrable_chargeDensity hχ hα)
    (RouteHessian.measurable_radialHessian hχ).aestronglyMeasurable
    (RouteHessian.norm_radialHessian_le hχ hM hη)).continuous

/-- The convolved Hessian belongs to `L∞`, with the same uniform bound. -/
theorem memLp_twoRadiusHessian_top {χ : ℂ → ℝ} {α η : ℝ}
    (hχ : IsMollifier χ) (hα : 0 < α) (hη : 0 < η) :
    MemLp (twoRadiusHessian χ α η) ∞ volume := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  exact memLp_top_of_bound (continuous_twoRadiusHessian hχ hα hη).aestronglyMeasurable
    (3 * (Real.pi * M / η ^ 2)) (Eventually.of_forall (norm_twoRadiusHessian_le hχ hM hα hη))

end MultipoleBKT

end
