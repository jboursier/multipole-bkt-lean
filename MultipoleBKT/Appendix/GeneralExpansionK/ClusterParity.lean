/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.LemmaI3
public import MultipoleBKT.Limits.MultIntegrable

/-!
# The radial cutoff of a cluster integrand of the model `0`

See (A.52). This module defines the original baseline integrand and
its measurability and finite-box bounds. The cutoff proof is in
`RouteAssembly.TailAssembly`, through the literal parity and U₀ expansion
and the case-F integration.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionK

open MeasureTheory Set Finset SimpleGraph Filter
open scoped ENNReal
open Limits SmallIntegral

variable {χ : ℂ → ℝ} {β lam M : ℝ}

/-! ### Bounds of the weights -/

/-- `e^{β C} + 1`, a bound of the pair weights `e^{-β v} 𝟙_𝒜` (`MultipoleBKT.dipoleBond_le`). -/
noncomputable def pairWeightBound (hχ : IsMollifier χ) (_hβ0 : 0 ≤ β) : ℝ :=
  Real.exp (β * Classical.choose (dipoleBond_le hχ)) + 1

theorem one_le_pairWeightBound (hχ : IsMollifier χ) (hβ0 : 0 ≤ β) :
    1 ≤ pairWeightBound hχ hβ0 := by
  unfold pairWeightBound
  linarith [Real.exp_pos (β * Classical.choose (dipoleBond_le hχ))]

theorem stablePairWeight_le_bound (hχ : IsMollifier χ) (hβ0 : 0 ≤ β) (hlam : 0 < lam)
    (d e : ℂ × ℂ) : stablePairWeight χ β lam d e ≤ pairWeightBound hχ hβ0 := by
  have h := (Classical.choose_spec (dipoleBond_le hχ)).2 β hβ0 lam hlam d e
  unfold pairWeightBound stablePairWeight
  linarith

section Weights

variable {ι β' : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype β'] [DecidableEq β']

open scoped Classical in
theorem abs_prod_blockW_le (hχ : IsMollifier χ) (hβ0 : 0 ≤ β) (hlam : 0 < lam) (blk : ι → β')
    (c : ι → ℂ × ℂ) :
    |∏ S, blockW χ β lam M blk S c| ≤
      pairWeightBound hχ hβ0 ^ (Fintype.card ι * Fintype.card ι * Fintype.card β') *
        (if ∀ S, ((nearGraph M lam c).induce {i | blk i = S}).Connected then 1 else 0) := by
  set W := pairWeightBound hχ hβ0
  have hW1 : 1 ≤ W := one_le_pairWeightBound hχ hβ0
  by_cases hall : ∀ S, ((nearGraph M lam c).induce {i | blk i = S}).Connected
  · rw [ite_eq_left hall, mul_one, pow_mul, abs_prod, ← Finset.card_univ (α := β'), ← prod_const]
    refine prod_le_prod₀ (fun S _ => abs_nonneg _) fun S _ => ?_
    unfold blockW
    rw [ite_eq_left (hall S), one_mul]
    refine abs_prod_prod_le _ fun i j => ?_
    split_ifs
    · rw [abs_of_nonneg (stablePairWeight_nonneg _ _ _ _ _)]
      exact stablePairWeight_le_bound hχ hβ0 hlam _ _
    · rw [abs_one]; exact hW1
  · rw [ite_eq_right hall, mul_zero]
    push Not at hall
    obtain ⟨S, hS⟩ := hall
    rw [prod_eq_zero (i := S) (mem_univ _) (by unfold blockW; rw [ite_eq_right hS, zero_mul]),
      abs_zero]

omit [Fintype ι] [DecidableEq ι] [LinearOrder ι] in
theorem linkIndE_nonneg (c : ι → ℂ × ℂ) (e : Sym2 ι) : 0 ≤ linkIndE M lam c e := by
  induction e using Sym2.ind with
  | h i j =>
    simp only [linkIndE, symmLift_mk, linkInd]
    split_ifs <;> norm_num

omit [Fintype ι] [DecidableEq ι] [LinearOrder ι] in
theorem linkIndE_le_one (c : ι → ℂ × ℂ) (e : Sym2 ι) : linkIndE M lam c e ≤ 1 := by
  induction e using Sym2.ind with
  | h i j =>
    simp only [linkIndE, symmLift_mk, linkInd]
    split_ifs <;> norm_num

omit [Fintype ι] [DecidableEq ι] [LinearOrder ι] in
theorem farInd_le_one (c : ι → ℂ × ℂ) (e : Sym2 ι) : farInd M lam c e ≤ 1 := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    show (if MultipoleLinked M lam (c i) (c j) then (0 : ℝ) else 1) ≤ 1
    split_ifs <;> norm_num

omit [Fintype ι] [LinearOrder ι] in
theorem linkIndE_flip (B : Finset ι) (c : ι → ℂ × ℂ) (e : Sym2 ι) :
    linkIndE M lam (flipCfg B c) e = linkIndE M lam c e := by
  induction e using Sym2.ind with
  | h i j =>
    simp only [linkIndE, symmLift_mk]
    exact linkInd_flip B c i j

omit [Fintype ι] [LinearOrder ι] in
theorem farInd_flip (B : Finset ι) (c : ι → ℂ × ℂ) (e : Sym2 ι) :
    farInd M lam (flipCfg B c) e = farInd M lam c e := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    show (if MultipoleLinked M lam (flipCfg B c i) (flipCfg B c j) then (0 : ℝ) else 1) =
      (if MultipoleLinked M lam (c i) (c j) then (0 : ℝ) else 1)
    exact if_congr (multipoleLinked_flip B c i j) rfl rfl

omit [Fintype ι] [LinearOrder ι] in
omit [DecidableEq ι] in
theorem measurable_linkIndE (M lam : ℝ) (e : Sym2 ι) :
    Measurable fun c : ι → ℂ × ℂ => linkIndE M lam c e := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    simp only [linkIndE, symmLift_mk, linkInd]
    exact Measurable.ite (measurableSet_multipoleLinked_apply M lam i j) measurable_const
      measurable_const

omit [Fintype ι] [DecidableEq ι] in
/-- The far bond `f_e 𝟙_{𝓑_e^c}` is bounded by `e^{β C}` (`dipBondExp`). -/
theorem abs_farBondE_le (hχ : IsMollifier χ) (hβ0 : 0 ≤ β) (hlam : 0 < lam) (c : ι → ℂ × ℂ)
    (e : Sym2 ι) : |farBondE χ β lam M c e| ≤ dipBondExp hχ hβ0 := by
  have hC0 := (Classical.choose_spec (abs_dipoleBond_sub_one_le hχ)).1
  have hC' := (Classical.choose_spec (abs_dipoleBond_sub_one_le hχ)).2
  have hB1 : 1 ≤ dipBondExp hχ hβ0 := Real.one_le_exp (mul_nonneg hβ0 hC0)
  induction e using Sym2.ind with
  | h i j =>
    simp only [farBondE, symmLift_mk, farBond]
    split_ifs
    · rw [abs_zero]; exact zero_le_one.trans hB1
    · unfold dipBond
      split_ifs
      · exact hC' β hβ0 lam hlam (c i) (c j)
      · exact hC' β hβ0 lam hlam (c j) (c i)

end Weights

/-! ### The integrand and its average over the reversals -/

section Average

variable {ι β' : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype β'] [DecidableEq β']

/-- The cluster integrand of the model `0` on blocks `blk`, with true bonds `Df`, far indicators
on `Dz` and near indicators `-𝟙_𝓑` on `Dn`. -/
noncomputable def clusterBox (χ : ℂ → ℝ) (β lam M : ℝ) (blk : ι → β')
    (Dn Dz Df : Finset (Sym2 ι)) (c : ι → ℂ × ℂ) : ℝ :=
  (∏ S, blockW χ β lam M blk S c) * (∏ e ∈ Df, farBondE χ β lam M c e) *
    (∏ e ∈ Dz, farInd M lam c e) * (∏ e ∈ Dn, -linkIndE M lam c e) *
    ∏ i, pairDensity χ β lam (c i)

omit [DecidableEq ι] in
theorem measurable_clusterBox (hχ : IsMollifier χ) (hlam : 0 < lam) (blk : ι → β')
    (Dn Dz Df : Finset (Sym2 ι)) : Measurable (clusterBox χ β lam M blk Dn Dz Df) := by
  unfold clusterBox
  refine Measurable.mul (Measurable.mul (Measurable.mul (Measurable.mul ?_ ?_) ?_) ?_) ?_
  · exact Finset.measurable_prod _ fun S _ => measurable_blockW hχ hlam blk S
  · exact Finset.measurable_prod _ fun e _ => measurable_farBondE hχ hlam β M e
  · exact Finset.measurable_prod _ fun e _ => measurable_farInd M lam e
  · exact Finset.measurable_prod _ fun e _ => (measurable_linkIndE M lam e).neg
  · exact Finset.measurable_prod _ fun i _ =>
      (measurable_pairDensity hχ hlam β).comp (measurable_pi_apply i)

/-- The cluster integrand is bounded (for fixed `λ`). -/
theorem exists_abs_clusterBox_le (hχ : IsMollifier χ) (hβ0 : 0 ≤ β) (hlam : 0 < lam)
    (blk : ι → β') (Dn Dz Df : Finset (Sym2 ι)) :
    ∃ B : ℝ, ∀ c, |clusterBox χ β lam M blk Dn Dz Df c| ≤ B := by
  classical
  obtain ⟨Cw, hCw0, hCw⟩ := exists_exp_smearedKernel_le hχ hβ0
  set P := Cw * lam ^ (-β)
  have hpd : ∀ d : ℂ × ℂ, pairDensity χ β lam d ≤ P := fun d => by
    refine (hCw lam hlam (d.1 - d.2)).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hlam (le_max_right _ _)
      (by linarith)) hCw0.le
  set W := pairWeightBound hχ hβ0
  set B := dipBondExp hχ hβ0
  have hB1 : 1 ≤ B :=
    Real.one_le_exp (mul_nonneg hβ0 (Classical.choose_spec (abs_dipoleBond_sub_one_le hχ)).1)
  refine ⟨W ^ (Fintype.card ι * Fintype.card ι * Fintype.card β') * B ^ Df.card *
    P ^ Fintype.card ι, fun c => ?_⟩
  unfold clusterBox
  have h1 := abs_prod_blockW_le (M := M) hχ hβ0 hlam blk c
  have h1' : |∏ S, blockW χ β lam M blk S c| ≤
      W ^ (Fintype.card ι * Fintype.card ι * Fintype.card β') := by
    refine h1.trans ?_
    have : 0 ≤ W ^ (Fintype.card ι * Fintype.card ι * Fintype.card β') :=
      pow_nonneg (zero_le_one.trans (one_le_pairWeightBound hχ hβ0)) _
    split_ifs
    · rw [mul_one]
    · rw [mul_zero]; exact this
  have h2 : |∏ e ∈ Df, farBondE χ β lam M c e| ≤ B ^ Df.card :=
    abs_prod_le_pow hB1 (fun e _ => abs_farBondE_le hχ hβ0 hlam c e) le_rfl
  have h3 : |∏ e ∈ Dz, farInd M lam c e| ≤ 1 := by
    rw [abs_prod]
    exact prod_le_one₀ (fun e _ => abs_nonneg _) fun e _ => by
      rw [abs_of_nonneg (farInd_nonneg c e)]; exact farInd_le_one c e
  have h4 : |∏ e ∈ Dn, -linkIndE M lam c e| ≤ 1 := by
    rw [abs_prod]
    exact prod_le_one₀ (fun e _ => abs_nonneg _) fun e _ => by
      rw [abs_neg, abs_of_nonneg (linkIndE_nonneg c e)]; exact linkIndE_le_one c e
  have h5 : |∏ i, pairDensity χ β lam (c i)| ≤ P ^ Fintype.card ι := by
    rw [abs_of_nonneg (prod_nonneg fun i _ => (pairDensity_pos _ _ _ _).le),
      ← Finset.card_univ (α := ι), ← prod_const]
    exact prod_le_prod₀ (fun i _ => (pairDensity_pos _ _ _ _).le) fun i _ => hpd _
  rw [abs_mul, abs_mul, abs_mul, abs_mul]
  have hW0 : 0 ≤ W ^ (Fintype.card ι * Fintype.card ι * Fintype.card β') :=
    pow_nonneg (zero_le_one.trans (one_le_pairWeightBound hχ hβ0)) _
  have hB0 : 0 ≤ B ^ Df.card := pow_nonneg (zero_le_one.trans hB1) _
  calc |∏ S, blockW χ β lam M blk S c| * |∏ e ∈ Df, farBondE χ β lam M c e| *
        |∏ e ∈ Dz, farInd M lam c e| * |∏ e ∈ Dn, -linkIndE M lam c e| *
        |∏ i, pairDensity χ β lam (c i)|
      ≤ W ^ (Fintype.card ι * Fintype.card ι * Fintype.card β') * B ^ Df.card * 1 * 1 *
          P ^ Fintype.card ι := by gcongr
    _ = _ := by ring

end Average

end ExpansionK

end MultipoleBKT

end
