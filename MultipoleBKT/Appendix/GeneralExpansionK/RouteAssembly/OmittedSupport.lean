/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteAssembly.MinusInfrastructure
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteOmitted.API
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteAssembly.TailExpansion

/-!
# Finite-box transfer for the omitted baseline

See Lemma A.7. Reversal averaging preserves the density and both cutoff
indicators. This identifies the original real integral with the baseline
average bounded by the quadratic omitted-domain estimates.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteAssembly

open MeasureTheory Set Finset SimpleGraph Limits Hierarchical Multipole Parity SmallIntegral
open RouteCases RouteOmitted
open scoped Classical ENNReal

/-- Internal transfer of an omitted-average estimate to the real baseline integral. -/
theorem internal_abs_integral_omitted_le {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] [Fintype κ] [DecidableEq κ] {χ : ℂ → ℝ} {β lam M : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hlam : 0 < lam)
    (blk : ι → κ) (Dn Dz Df : Finset (Sym2 ι)) (h : ℝ) {N : ℕ} {K : ℝ}
    (hK : 0 ≤ K)
    (hint : (∫⁻ c in boxConfig ι N,
      ENNReal.ofReal |omittedAverage χ β lam M h blk Dn Dz Df c|) ≤ ENNReal.ofReal K) :
    |∫ c in boxConfig ι N, clusterQ β (dipoleInteraction χ lam) (fun _ => 1)
      M lam blk Dn Dz Df c * (((∏ i, pairDensity χ β lam (c i)) * cutInd h c) *
        (1-shortInd (17*h) Df c))| ≤ K := by
  let F (c : ι → ℂ × ℂ) := clusterBox χ β lam M blk Dn Dz Df c *
    (cutInd h c * (1-shortInd (17*h) Df c))
  obtain ⟨B, hB⟩ := exists_abs_clusterBox_le (M := M) hχ hβ hlam blk Dn Dz Df
  have hm : Measurable F := (measurable_clusterBox (β := β) (M := M) hχ hlam blk Dn Dz Df).mul
    ((measurable_cutInd h).mul (measurable_const.sub (measurable_shortInd (17*h) Df)))
  have hb (c : ι → ℂ × ℂ) : |F c| ≤ B := by
    have hc0 := cutInd_nonneg h c
    have hs0 : 0 ≤ 1-shortInd (17*h) Df c := sub_nonneg.2 (shortInd_le_one _ _ _)
    have hc1 : cutInd h c * (1-shortInd (17*h) Df c) ≤ 1 := by
      exact (mul_le_mul (cutInd_le_one h c) (sub_le_self _ (shortInd_nonneg _ _ _)) hs0 zero_le_one).trans_eq (mul_one _)
    dsimp only [F]
    rw [abs_mul, abs_of_nonneg (mul_nonneg hc0 hs0)]
    exact (mul_le_mul_of_nonneg_right (hB c) (mul_nonneg hc0 hs0)).trans
      ((mul_le_mul_of_nonneg_left hc1 ((abs_nonneg _).trans (hB c))).trans_eq (mul_one _))
  have he (c : ι → ℂ × ℂ) : clusterQ β (dipoleInteraction χ lam) (fun _ => 1)
      M lam blk Dn Dz Df c * (((∏ i, pairDensity χ β lam (c i)) * cutInd h c) *
        (1-shortInd (17*h) Df c)) = F c := by
    dsimp only [F]
    rw [clusterBox_eq_clusterQ]
    ring
  simp_rw [he]
  apply abs_integral_le_of_avg blk hm hb N
    (fun c => ENNReal.ofReal |omittedAverage χ β lam M h blk Dn Dz Df c|) _ hK hint
  intro c
  have hf (A : Finset κ) : F (flipCfg (blockLabels blk A) c) =
      clusterQ β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz Df
        (flipCfg (blockLabels blk A) c) * omittedDensity χ β lam h Df c := by
    dsimp only [F, omittedDensity]
    rw [clusterBox_eq_clusterQ]
    rw [cutInd_flip, shortInd_flip]
    have hp : (∏ i, pairDensity χ β lam (flipCfg (blockLabels blk A) c i)) =
        ∏ i, pairDensity χ β lam (c i) :=
      prod_congr rfl fun i _ => pairDensity_flip hχ _ c i
    rw [hp]
    ring
  simp_rw [hf, ← sum_mul, mul_div_right_comm]
  exact le_rfl

end MultipoleBKT.ExpansionK.RouteAssembly

end
