/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteDirect.Integrable

/-!
# The parity majorant, for a general block weight

See Lemma A.5. A bounded measurable integrand is integrable in each finite
box, and averaging over the reversals of any block system preserves that
integral. The logarithmic majorant is proved in `Limits/RouteDirect/Integrable`.
-/

@[expose] public section

namespace MultipoleBKT

namespace SmallIntegral

open MeasureTheory Set Finset SimpleGraph Filter
open scoped ENNReal
open Limits

variable {χ : ℂ → ℝ} {β lam M : ℝ}

section Average

variable {ι β' : Type*} [Fintype ι] [DecidableEq ι] [Fintype β'] [DecidableEq β']

omit [DecidableEq ι] in
theorem volume_boxConfig_ne_top (N : ℕ) : volume (boxConfig ι N) ≠ ⊤ := by
  rw [boxConfig, volume_pi, Measure.pi_pi]
  exact ENNReal.prod_ne_top fun _ _ => (volume_box_prod_lt_top N).ne

omit [DecidableEq ι] in
/-- A bounded measurable integrand is integrable on `(Λ²)^ι`. -/
theorem integrableOn_boxConfig_of_bounded {F : (ι → ℂ × ℂ) → ℝ} (hF : Measurable F) {B : ℝ}
    (hB : ∀ c, |F c| ≤ B) (N : ℕ) : IntegrableOn F (boxConfig ι N) :=
  Measure.integrableOn_of_bounded (volume_boxConfig_ne_top N) hF.aestronglyMeasurable (M := B)
    (Eventually.of_forall fun c => by rw [Real.norm_eq_abs]; exact hB c)

omit [Fintype β'] in
/-- Averaging a bounded integrand over the reversals of the blocks does not change its box
integral (the reversals preserve `(Λ²)^ι`). -/
theorem integral_boxConfig_avg_flip (blk : ι → β') {F : (ι → ℂ × ℂ) → ℝ} (hF : Measurable F)
    {B : ℝ} (hB : ∀ c, |F c| ≤ B) (N : ℕ) [Fintype β'] :
    ∫ c in boxConfig ι N, (∑ A : Finset β', F (flipCfg (blockLabels blk A) c)) /
        2 ^ Fintype.card β' =
      ∫ c in boxConfig ι N, F c := by
  have hint : ∀ A : Finset β', IntegrableOn (fun c => F (flipCfg (blockLabels blk A) c))
      (boxConfig ι N) := fun A =>
    integrableOn_boxConfig_of_bounded (hF.comp (measurable_flipCfg _)) (fun c => hB _) N
  rw [integral_div, integral_finsetSum _ fun A _ => hint A]
  simp_rw [integral_boxConfig_flipCfg]
  rw [sum_const, card_univ, Fintype.card_finset, nsmul_eq_mul]
  push_cast
  field_simp

end Average

end SmallIntegral

end MultipoleBKT

end
