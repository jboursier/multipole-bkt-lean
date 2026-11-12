/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteAssembly.CutoffBoundary
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteAssembly.MixedMeasurable

/-!
# The parity and nonempty-U₀ expansion of the cutoff difference

See (A.52)
and (A.53). The original averaged integrand is
expanded into its cut-even subsets and literal closed tail products.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteAssembly

open MeasureTheory Set Finset Limits Hierarchical Multipole Parity SmallIntegral RouteCases RouteSpatial
open scoped Classical ENNReal

variable {I B : Type*} [Fintype I] [DecidableEq I] [LinearOrder I] [Fintype B] [DecidableEq B]
variable {χ : ℂ → ℝ} {β lam M : ℝ}

/-- Identify the original baseline cluster integrand before averaging. -/
theorem clusterBox_eq_clusterQ (blk : I → B) (Dn Dz Df : Finset (Sym2 I)) (c : I → ℂ × ℂ) :
    clusterBox χ β lam M blk Dn Dz Df c =
      clusterQ β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz Df c *
        ∏ i, pairDensity χ β lam (c i) := by
  have hb (S : B) : blockWW β (dipoleInteraction χ lam) (fun _ => 1) M lam blk S c =
      blockW χ β lam M blk S c := by
    simp only [blockWW,blockW,nearConnInd,ite_self,prod_const_one,mul_one]
    congr 1
    · split_ifs <;> rfl
  have hf (e : Sym2 I) : farBondW β (dipoleInteraction χ lam) M lam c e = farBondE χ β lam M c e := by
    induction e using Sym2.ind with
    | h i j =>
      simp only [farBondW,farBondE,symmLift_mk,farBondWij,farBond,sOrd,dipBond]
      split_ifs <;> rfl
  unfold clusterBox clusterQ clusterG
  simp only [hb,hf]
  ring

/-- Reversal cancellation with the original baseline density. -/
theorem avg_clusterBox_eq (hχ : IsMollifier χ) (hM : 1 ≤ M)
    (blk : I → B) (Dn Dz Df : Finset (Sym2 I)) (c : I → ℂ × ℂ) :
    (∑ A : Finset B, clusterBox χ β lam M blk Dn Dz Df (flipCfg (blockLabels blk A) c)) /
      2^Fintype.card B = ∑ O ∈ Df.powerset.filter (CutEven (Sym2.map blk)),
        baselineParityIntegrand χ β lam M blk Dn Dz Df O c := by
  simp_rw [clusterBox_eq_clusterQ,clusterQ_flip (ψ := fun _ => 1) hM
    (fun d e => Limits.dipoleInteraction_swap_left d e hχ lam)
    (fun d e => Limits.dipoleInteraction_swap_right d e hχ lam) (fun _ => rfl),
    pairDensity_flip hχ _ c]
  rw [← sum_mul,← mul_sum]
  rw [show (clusterG β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz c *
      ∑ A : Finset B, ∏ e ∈ Df, (alphaW β (dipoleInteraction χ lam) M lam c e + linkIndE M lam c e +
        signCross (Sym2.map blk) A e * gammaW β (dipoleInteraction χ lam) M lam c e)) *
        (∏ i, pairDensity χ β lam (c i)) / 2^Fintype.card B =
      clusterG β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz c *
        ((∑ A : Finset B, ∏ e ∈ Df, (alphaW β (dipoleInteraction χ lam) M lam c e + linkIndE M lam c e +
          signCross (Sym2.map blk) A e * gammaW β (dipoleInteraction χ lam) M lam c e)) / 2^Fintype.card B) *
        (∏ i, pairDensity χ β lam (c i)) by ring]
  rw [RouteCases.avg_product_eq_cutEven,mul_sum,sum_mul]
  apply sum_congr rfl
  intro O _
  rfl

/-- Exact finite expansion of the averaged cutoff difference, with closed U₀. -/
theorem avg_clusterBox_cutoff_expansion_ae (hχ : IsMollifier χ) (hM : 1 ≤ M)
    (blk : I → B) (Dn Dz Df : Finset (Sym2 I)) (h : ℝ) :
    (fun c : I → ℂ × ℂ => (∑ A : Finset B,
      clusterBox χ β lam M blk Dn Dz Df (flipCfg (blockLabels blk A) c) *
        (cutInd h (flipCfg (blockLabels blk A) c)-1)) / 2^Fintype.card B) =ᵐ[volume]
    (fun c => ∑ U ∈ (univ : Finset I).powerset.erase ∅,
      ∑ O ∈ Df.powerset.filter (CutEven (Sym2.map blk)),
        baselineParityIntegrand χ β lam M blk Dn Dz Df O c * tailProduct true h U c) := by
  filter_upwards [cutoff_nonempty_expansion_ae (I := I) h] with c hc
  simp_rw [cutInd_flip]
  rw [← sum_mul,mul_div_right_comm,avg_clusterBox_eq hχ hM,hc,mul_sum]
  apply sum_congr rfl
  intro U _
  rw [sum_mul]

/-- The baseline parity term and every signed tail product are measurable. -/
theorem measurable_baseline_tail (hχ : IsMollifier χ) (hlam : 0 < lam)
    (blk : I → B) (Dn Dz Df O : Finset (Sym2 I)) (h : ℝ) (U : Finset I) :
    Measurable (fun c : I → ℂ × ℂ => baselineParityIntegrand χ β lam M blk Dn Dz Df O c *
      tailProduct true h U c) := by
  have hg : Measurable (clusterG β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz : (I → ℂ × ℂ) → ℝ) := by
    unfold clusterG
    exact ((Finset.measurable_prod _ fun _ _ => measurable_blockWW (measurable_dipoleInteraction hχ hlam)
      measurable_const blk _).mul (Finset.measurable_prod _ fun e _ => measurable_farInd M lam e)).mul
        (Finset.measurable_prod _ fun e _ => (measurable_linkIndE M lam e).neg)
  have hparts (e : Sym2 I) : Measurable (fun c : I → ℂ × ℂ => gammaW β (dipoleInteraction χ lam) M lam c e) ∧
      Measurable (fun c : I → ℂ × ℂ => alphaW β (dipoleInteraction χ lam) M lam c e + linkIndE M lam c e) := by
    induction e using Sym2.ind with
    | h i j =>
      have hw : Measurable (fun c : I → ℂ × ℂ => wOrd (dipoleInteraction χ lam) c i j) := by
        unfold wOrd
        split_ifs
        · exact measurable_dipoleInteraction_apply hχ hlam i j
        · exact measurable_dipoleInteraction_apply hχ hlam j i
      simp only [gammaW,alphaW,symmLift_mk]
      exact ⟨Measurable.ite (measurableSet_multipoleLinked_apply M lam i j) measurable_const
        ((Real.measurable_sinh.comp (measurable_const.mul hw)).neg),
        (Measurable.ite (measurableSet_multipoleLinked_apply M lam i j) measurable_const
          ((Real.measurable_cosh.comp (measurable_const.mul hw)).sub_const 1)).add (measurable_linkIndE M lam s(i,j))⟩
  have hp : Measurable (tailProduct true h U : (I → ℂ × ℂ) → ℝ) := by
    unfold tailProduct
    exact Finset.measurable_prod _ fun i _ => (Measurable.ite
      (measurableSet_le measurable_const (by fun_prop)) measurable_const measurable_const).neg
  exact (((hg.mul ((Finset.measurable_prod _ fun e _ => (hparts e).1).mul
    (Finset.measurable_prod _ fun e _ => (hparts e).2))).mul
      (Finset.measurable_prod _ fun i _ => (measurable_pairDensity hχ hlam β).comp (measurable_pi_apply i))).mul hp)

omit [DecidableEq I] [LinearOrder I] in
/-- A nonempty strict tail product is bounded by the strict maximum-radius tail. -/
theorem tailProduct_strict_bound (h lam : ℝ) (U : Finset I) (hU : U.Nonempty) (c : I → ℂ × ℂ) :
    |tailProduct false h U c| ≤ (if h < maxRad lam c then (1 : ℝ) else 0) := by
  by_cases ht : h < maxRad lam c
  · rw [ite_eq_left ht]
    unfold tailProduct
    rw [abs_prod]
    exact prod_le_one₀ (fun _ _ => abs_nonneg _) fun i _ => by split_ifs <;> norm_num
  · obtain ⟨i,hi⟩ := hU
    have hn : ¬ h < ‖(c i).1-(c i).2‖ := by
      intro hh
      exact ht (hh.trans_le ((le_max_left _ _).trans (rhoD_le_maxRad lam c i)))
    rw [ite_eq_right ht]
    have hz : tailProduct false h U c = 0 := by
      unfold tailProduct
      exact prod_eq_zero hi (by simp only [Bool.false_eq_true,↓reduceIte,ite_eq_right hn,neg_zero])
    rw [hz,abs_zero]

end MultipoleBKT.ExpansionK.RouteAssembly

end
