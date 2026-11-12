/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Sum

/-!
# Finite sums under the lower-model integral

The proof of Lemma 4.57. These internal integration
identities move the finite group and tree sums across Lebesgue integration.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RouteMerge

open MeasureTheory Finset
open scoped ENNReal

variable {α ι : Type*} [MeasurableSpace α] (μ : Measure α)

/-- The finite sum inequality does not require measurability. -/
theorem sum_integrals_le [DecidableEq ι] (s : Finset ι) (f : ι → α → ℝ)
    (hf : ∀ i ∈ s, ∀ x, 0 ≤ f i x) :
    (∑ i ∈ s, ∫⁻ x, ENNReal.ofReal (f i x) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (∑ i ∈ s, f i x) ∂μ := by
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => hf i hi _)]
  exact sum_lintegral_le μ s _

/-- Measurable finite sums commute with integration. -/
theorem integral_sum [DecidableEq ι] (s : Finset ι) (f : ι → α → ℝ)
    (hf : ∀ i ∈ s, ∀ x, 0 ≤ f i x) (hm : ∀ i ∈ s, Measurable (f i)) :
    (∫⁻ x, ENNReal.ofReal (∑ i ∈ s, f i x) ∂μ) =
      ∑ i ∈ s, ∫⁻ x, ENNReal.ofReal (f i x) ∂μ := by
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => hf i hi _)]
  exact lintegral_finsetSum _ (fun i hi => ENNReal.measurable_ofReal.comp (hm i hi))

/-- Scalar multiplication, including a factorial reciprocal. -/
theorem integral_mul (a : ℝ) (ha : 0 ≤ a) (f : α → ℝ) :
    (∫⁻ x, ENNReal.ofReal (a * f x) ∂μ) =
      ENNReal.ofReal a * ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  simp_rw [ENNReal.ofReal_mul ha]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end MultipoleBKT.AbsoluteLower.RouteMerge

end
