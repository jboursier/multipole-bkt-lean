/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.FrozenMixed

/-!
# Common block and support factors in the mixed summands

See (A.55)–(A.58). The stable intra-block Boltzmann factors are bounded by
a uniform coefficient. Block connectivity, near bonds, far supports and
the dipole density remain explicit.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset Limits Hierarchical SmallIntegral

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype κ] [DecidableEq κ]

/-- The common spatial support of the original cluster integrands. -/
noncomputable def clusterSupport (M lam : ℝ) (blk : ι → κ)
    (Dn Dz : Finset (Sym2 ι)) (c : ι → ℂ × ℂ) : ℝ :=
  (∏ S, nearConnInd M lam blk S c) *
    (∏ e ∈ Dz, farInd M lam c e) * ∏ e ∈ Dn, linkIndE M lam c e

omit [LinearOrder ι] in
/-- Every common support factor is nonnegative. -/
theorem clusterSupport_nonneg (M lam : ℝ) (blk : ι → κ)
    (Dn Dz : Finset (Sym2 ι)) (c : ι → ℂ × ℂ) :
    0 ≤ clusterSupport M lam blk Dn Dz c := by
  classical
  apply mul_nonneg (mul_nonneg ?_ (prod_nonneg fun e _ => farInd_nonneg c e))
    (prod_nonneg fun e _ => linkIndE_nonneg c e)
  apply prod_nonneg
  intro S _
  unfold nearConnInd
  split_ifs <;> norm_num

/-- The common intra-block baseline is uniformly bounded while retaining every
support indicator. The coefficient is independent of the frozen data. -/
theorem clusterG_baseline_common {χ : ℂ → ℝ} {β lam M : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hlam : 0 < lam)
    (blk : ι → κ) (Dn Dz : Finset (Sym2 ι)) (c : ι → ℂ × ℂ) :
    |clusterG β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz c| ≤
      Real.exp (β * cbK hχ) ^ (Fintype.card ι * Fintype.card ι) *
        clusterSupport M lam blk Dn Dz c := by
  classical
  let W := Real.exp (β * cbK hχ)
  have hW : 1 ≤ W := Real.one_le_exp (mul_nonneg hβ (cbK_nonneg hχ))
  let a := fun i j => if blk i = blk j ∧ i < j then
    stableWeight β (dipoleInteraction χ lam) (c i) (c j) else 1
  have ha0 : ∀ i j, 0 ≤ a i j := by
    intro i j
    dsimp [a]
    split_ifs
    · exact stableWeight_nonneg _ _ _ _
    · exact zero_le_one
  have haW : ∀ i j, a i j ≤ W := by
    intro i j
    dsimp [a]
    split_ifs
    · unfold stableWeight
      split_ifs with hst
      · exact Real.exp_le_exp.2 (by nlinarith [neg_cbK_le hχ hlam hst])
      · exact (Real.exp_pos _).le
    · exact hW
  have hprod : (∏ i, ∏ j, a i j) ≤ W ^ (Fintype.card ι * Fintype.card ι) := by
    calc _ ≤ ∏ _i : ι, ∏ _j : ι, W :=
           prod_le_prod₀ (fun i _ => prod_nonneg fun j _ => ha0 i j)
             (fun i _ => prod_le_prod₀ (fun j _ => ha0 i j) (fun j _ => haW i j))
         _ = _ := by simp only [prod_const, card_univ]; rw [← pow_mul]
  have hnear : 0 ≤ ∏ S, nearConnInd M lam blk S c := by
    apply prod_nonneg
    intro S _
    unfold nearConnInd
    split_ifs <;> norm_num
  have hfar : 0 ≤ ∏ e ∈ Dz, farInd M lam c e := prod_nonneg (fun e (_ : e ∈ Dz) => farInd_nonneg c e)
  have hexact : |clusterG β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz c| =
      clusterSupport M lam blk Dn Dz c * (∏ i, ∏ j, a i j) := by
    have hneg : |∏ e ∈ Dn, -linkIndE M lam c e| = ∏ e ∈ Dn, linkIndE M lam c e := by
      rw [abs_prod]
      exact prod_congr rfl fun e _ => by rw [abs_neg, abs_of_nonneg (linkIndE_nonneg c e)]
    unfold clusterG
    rw [prod_blockWW_eq]
    change |(∏ S, nearConnInd M lam blk S c) *
      ((∏ i, ∏ j, a i j) * (∏ _i : ι, (1 : ℝ))) *
      (∏ e ∈ Dz, farInd M lam c e) * (∏ e ∈ Dn, -linkIndE M lam c e)| = _
    simp only [prod_const_one, mul_one, abs_mul, abs_of_nonneg hnear, abs_of_nonneg hfar,
      abs_of_nonneg (prod_nonneg fun i _ => prod_nonneg fun j _ => ha0 i j), hneg]
    dsimp [clusterSupport, a]
    ring
  rw [hexact]
  exact (mul_le_mul_of_nonneg_left hprod (clusterSupport_nonneg M lam blk Dn Dz c)).trans_eq (mul_comm _ _)

end MultipoleBKT.ExpansionK.RouteCases

end
