/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.MinusParity

/-!
# Finite-box averaging and density bounds

See Lemma A.7. Reversal averaging bounds a real integral by the lower integral of
its averaged absolute value. The elementary density bound supplies
finite-box integrability in the integral estimates.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionK

open MeasureTheory Set Finset SimpleGraph Filter
open scoped ENNReal
open Hierarchical Multipole Parity Limits SmallIntegral Appendix

variable {χ : ℂ → ℝ} {β lam M : ℝ}

/-! ### Auxiliary bounds -/

section Aux

variable {ι β' : Type*} [Fintype ι] [DecidableEq ι] [Fintype β'] [DecidableEq β']

/-- An integral bounded through the average over the reversals of the blocks. -/
theorem abs_integral_le_of_avg (blk : ι → β') {F : (ι → ℂ × ℂ) → ℝ} (hF : Measurable F) {B : ℝ}
    (hB : ∀ c, |F c| ≤ B) (N : ℕ) (G : (ι → ℂ × ℂ) → ℝ≥0∞)
    (hG : ∀ c, ENNReal.ofReal |(∑ A : Finset β', F (flipCfg (blockLabels blk A) c)) /
      2 ^ Fintype.card β'| ≤ G c) {K : ℝ} (hK : 0 ≤ K)
    (hint : ∫⁻ c in boxConfig ι N, G c ≤ ENNReal.ofReal K) :
    |∫ c in boxConfig ι N, F c| ≤ K := by
  rw [← integral_boxConfig_avg_flip blk hF hB N, ← Real.norm_eq_abs]
  refine (norm_integral_le_lintegral_norm (fun c => (∑ A : Finset β',
    F (flipCfg (blockLabels blk A) c)) / 2 ^ Fintype.card β')).trans ?_
  refine ENNReal.toReal_le_of_le_ofReal hK ((lintegral_mono fun c => ?_).trans hint)
  rw [Real.norm_eq_abs]
  exact hG c

omit [DecidableEq ι] in
theorem prod_pairDensity_le (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hlam : 0 < lam)
    (c : ι → ℂ × ℂ) : ∏ i, pairDensity χ β lam (c i) ≤
      (densConst hχ hβ * lam ^ (-β)) ^ Fintype.card ι := by
  have hd : ∀ i, pairDensity χ β lam (c i) ≤ densConst hχ hβ * lam ^ (-β) := fun i => by
    refine (exp_le_densConst hχ hβ hlam ((c i).1 - (c i).2)).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hlam (le_max_right _ _)
      (by linarith)) (densConst_pos hχ hβ).le
  calc ∏ i, pairDensity χ β lam (c i) ≤ ∏ _i : ι, densConst hχ hβ * lam ^ (-β) :=
        prod_le_prod₀ (fun i _ => (pairDensity_pos _ _ _ _).le) fun i _ => hd i
    _ = _ := by rw [prod_const, card_univ]

end Aux

end ExpansionK

end MultipoleBKT

end
