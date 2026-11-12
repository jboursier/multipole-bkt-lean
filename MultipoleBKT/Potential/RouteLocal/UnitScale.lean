/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.Regularity
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Unit-scale decomposition of a neutral self-interaction

See Proposition 3.3,
(3.13) and (3.14). Scale the two equal radii to one,
expand the neutral interaction into the two translated averages of the singly
smoothed potential, and integrate its Taylor expansion. The linear average
vanishes because the gradient is odd and the charge is even.
-/

@[expose] public section

open MeasureTheory Metric
open scoped RealInnerProductSpace

namespace MultipoleBKT.RouteLocal

variable {χ : ℂ → ℝ}

/-- The linear term in the averaged Taylor expansion vanishes, by the
odd-field average identity (equation (3.14)). -/
theorem integral_gradient_inner_eq_zero (hχ : IsMollifier χ) (z : ℂ) :
    ∫ x, ⟪smearedField χ 1 x, z⟫ ∂smearedCharge χ 0 1 = 0 := by
  have := isProbabilityMeasure_smearedCharge hχ 0 one_pos
  obtain ⟨M, hM⟩ := hχ.exists_bound
  have hi : Integrable (smearedField χ 1) (smearedCharge χ 0 1) :=
    (integrable_const (Real.sqrt (Real.pi * M) / 1)).mono'
      (continuous_smearedField hχ one_pos).aestronglyMeasurable
      (Filter.Eventually.of_forall (norm_smearedField_le hχ hM one_pos))
  calc _ = ∫ x, ⟪z, smearedField χ 1 x⟫ ∂smearedCharge χ 0 1 :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => real_inner_comm _ _)
    _ = ⟪z, ∫ x, smearedField χ 1 x ∂smearedCharge χ 0 1⟫ := integral_inner hi z
    _ = 0 := by rw [integral_smearedField_smearedCharge hχ, inner_zero_right]

/-- Averaging the singly smoothed Taylor remainder gives the quadratic
error, with exactly the constant of Lemma 3.1. -/
theorem abs_integral_unit_increment_le (hχ : IsMollifier χ) {M : ℝ}
    (hM : ∀ x, χ x ≤ M) (z : ℂ) :
    |∫ x, (smearedPotential χ 1 (x + z) - smearedPotential χ 1 x)
      ∂smearedCharge χ 0 1| ≤ 3 * (Real.pi * M) * ‖z‖ ^ 2 := by
  have := isProbabilityMeasure_smearedCharge hχ 0 one_pos
  have hi := integrable_smearedPotential_comp hχ one_pos (f := fun x => x + z)
    (continuous_id.add continuous_const) 0 1
  have hj := integrable_smearedPotential_comp hχ one_pos (f := fun x => x) continuous_id 0 1
  have hg := integrable_smearedCharge_of_continuous hχ
    (f := fun x => ⟪smearedField χ 1 x, z⟫)
    ((continuous_smearedField hχ one_pos).inner continuous_const) 0 1
  have he : (∫ x, (smearedPotential χ 1 (x + z) - smearedPotential χ 1 x)
      ∂smearedCharge χ 0 1) =
      ∫ x, (smearedPotential χ 1 (x + z) - smearedPotential χ 1 x -
        ⟪smearedField χ 1 x, z⟫) ∂smearedCharge χ 0 1 := by
    have hd : Integrable (fun x => smearedPotential χ 1 (x + z) - smearedPotential χ 1 x)
        (smearedCharge χ 0 1) := hi.sub hj
    rw [integral_sub hd hg, integral_gradient_inner_eq_zero hχ, sub_zero]
  rw [he, ← Real.norm_eq_abs]
  calc _ ≤ 3 * (Real.pi * M) * ‖z‖ ^ 2 * (smearedCharge χ 0 1).real Set.univ :=
      norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact abs_smearedPotential_one_sub_sub_inner_le hχ hM x z)
    _ = _ := by rw [probReal_univ, mul_one]

/-- A translated charge average is the integral of the increment of the
singly smoothed potential (3.14). -/
theorem unit_increment_eq_integral (hχ : IsMollifier χ) (z : ℂ) :
    twoRadiusKernel χ 1 1 z - twoRadiusKernel χ 1 1 0 =
      ∫ x, (smearedPotential χ 1 (x + z) - smearedPotential χ 1 x)
        ∂smearedCharge χ 0 1 := by
  have hneg := map_neg_smearedCharge hχ 0 1
  rw [neg_zero] at hneg
  have he (w : ℂ) : twoRadiusKernel χ 1 1 w =
      ∫ x, smearedPotential χ 1 (x + w) ∂smearedCharge χ 0 1 := by
    rw [twoRadiusKernel_eq_integral_smearedPotential hχ]
    conv_lhs => rw [← hneg]
    rw [measurableEmbedding_neg.integral_map]
    simp only [sub_neg_eq_add, add_comm]
  simp only [he z, he 0, add_zero]
  rw [integral_sub
    (integrable_smearedPotential_comp hχ one_pos (f := fun x => x + z)
      (continuous_id.add continuous_const) 0 1)
    (integrable_smearedPotential_comp hχ one_pos (f := fun x => x) continuous_id 0 1)]

/-- The two terms in (3.14), at `z` and `-z`, expressed as actual
averages of the singly smoothed potential. -/
theorem unit_neutral_decomposition (hχ : IsMollifier χ) (z : ℂ) :
    2 * twoRadiusKernel χ 1 1 0 - twoRadiusKernel χ 1 1 z -
        twoRadiusKernel χ 1 1 (-z) =
      -(∫ x, (smearedPotential χ 1 (x + -z) - smearedPotential χ 1 x)
        ∂smearedCharge χ 0 1) -
      (∫ x, (smearedPotential χ 1 (x + z) - smearedPotential χ 1 x)
        ∂smearedCharge χ 0 1) := by
  rw [← unit_increment_eq_integral hχ, ← unit_increment_eq_integral hχ]
  ring

/-- Scaling of the neutral self-interaction, (3.13).
The additive logarithm cancels by neutrality. -/
theorem neutral_scale_one (hχ : IsMollifier χ) {τ : ℝ} (hτ : 0 < τ) (w : ℂ) :
    2 * twoRadiusKernel χ τ τ 0 - twoRadiusKernel χ τ τ w -
        twoRadiusKernel χ τ τ (-w) =
      2 * twoRadiusKernel χ 1 1 0 - twoRadiusKernel χ 1 1 (w / τ) -
        twoRadiusKernel χ 1 1 (-(w / τ)) := by
  simp only [twoRadiusKernel_self]
  rw [smearedKernel_eq_logKernel_add hχ hτ 0,
    smearedKernel_eq_logKernel_add hχ hτ w,
    smearedKernel_eq_logKernel_add hχ hτ (-w), zero_div, neg_div]
  ring

/-- The normalized displacement has the length specified after (3.13). -/
theorem norm_unit_displacement {τ : ℝ} (hτ : 0 < τ) (w : ℂ) :
    ‖w / (τ : ℂ)‖ = ‖w‖ / τ := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]

/-- The absolute quadratic error asserted by (3.12), obtained by
scaling to one and averaging the singly smoothed Taylor expansion. -/
theorem abs_neutral_self_le_sq (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    {τ : ℝ} (hτ : 0 < τ) (w : ℂ) :
    |2 * twoRadiusKernel χ τ τ 0 - twoRadiusKernel χ τ τ w -
        twoRadiusKernel χ τ τ (-w)| ≤
      6 * (Real.pi * M) * (‖w‖ / τ) ^ 2 := by
  rw [neutral_scale_one hχ hτ, unit_neutral_decomposition hχ]
  have hp := abs_integral_unit_increment_le hχ hM (w / τ)
  have hm := abs_integral_unit_increment_le hχ hM (-(w / τ))
  rw [norm_neg, norm_unit_displacement hτ] at hm
  rw [norm_unit_displacement hτ] at hp
  calc _ ≤ |-(∫ x, (smearedPotential χ 1 (x + -(w / τ)) - smearedPotential χ 1 x)
        ∂smearedCharge χ 0 1)| +
      |∫ x, (smearedPotential χ 1 (x + w / τ) - smearedPotential χ 1 x)
        ∂smearedCharge χ 0 1| := abs_sub _ _
    _ ≤ 3 * (Real.pi * M) * (‖w‖ / τ) ^ 2 +
        3 * (Real.pi * M) * (‖w‖ / τ) ^ 2 := by rw [abs_neg]; exact add_le_add hm hp
    _ = _ := by ring

/-- The upper side of (3.12), used in the lower bound on energy. -/
theorem neutral_self_le_sq (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    {τ : ℝ} (hτ : 0 < τ) (w : ℂ) :
    2 * twoRadiusKernel χ τ τ 0 - twoRadiusKernel χ τ τ w -
        twoRadiusKernel χ τ τ (-w) ≤
      6 * (Real.pi * M) * (‖w‖ / τ) ^ 2 :=
  (le_abs_self _).trans (abs_neutral_self_le_sq hχ hM hτ w)

end MultipoleBKT.RouteLocal

end
