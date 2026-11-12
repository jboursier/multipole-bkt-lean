/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.CutoffModel

/-!
# Transfer from the truncated zero model

See the proof of
Proposition 4.23. First use the chain with a finite cutoff,
then include its integral in the untruncated numerator before normalization.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegral.RouteChain

open MeasureTheory Set Finset
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {χ : ℂ → ℝ} {β M : ℝ}

/-- Including the finite cutoff in the untruncated integral.
The same untruncated normalization is used on both sides when forming `𝖬`. -/
theorem multipoleIntegralCut_le (hχ : IsMollifier χ) {lam : ℝ} (hlam : 0 < lam)
    (N : ℕ) (β M h : ℝ) (S : Finset ℕ) :
    multipoleIntegralCut χ N β lam M h S ≤ multipoleIntegral χ N β lam M S := by
  unfold multipoleIntegralCut multipoleIntegral
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (cutIntegrand_nonneg lam h))
      (measurable_cutIntegrand hχ hlam β M h).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall multipoleIntegrand_nonneg)
      (measurable_multipoleIntegrand hχ hlam β M).aestronglyMeasurable]
  exact ENNReal.toReal_mono (lintegral_multipoleIntegrand_ne_top hχ hlam N β M S)
    (lintegral_mono fun c => ENNReal.ofReal_le_ofReal (cutIntegrand_le lam h c))

/-- The original transfer of the lower bound through a finite cutoff. -/
theorem le_multipoleIntegral_via_cutoff (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ}
    (hk : 1 ≤ k) (hM : 9 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ S : Finset ℕ, S.card = k →
        C⁻¹ * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) ≤ multipoleIntegral χ N β lam M S := by
  obtain ⟨C, hC, h⟩ := le_multipoleIntegralCut_chain hχ hβ hk hM
  refine ⟨C, hC, fun lam hlam => ?_⟩
  obtain ⟨N₀, hN₀⟩ := h lam hlam
  exact ⟨N₀, fun N hN S hS => (hN₀ N hN (2 * lam) le_rfl S hS).trans
    (multipoleIntegralCut_le hχ hlam N β M (2 * lam) S)⟩

end MultipoleBKT.MultipoleIntegral.RouteChain

end
