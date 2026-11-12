/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.MinusPointwise
public import MultipoleBKT.Appendix.GeneralExpansionK.TailIntegral
public import MultipoleBKT.Appendix.GeneralExpansionK.LemmaI3

/-!
# Measurability and support of the model integrands

See Lemma A.7. The short-edge indicator and cluster weights are measurable and bounded.
Their reversal identities preserve the common integration domain.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionK

open MeasureTheory Set Finset SimpleGraph
open scoped ENNReal
open Hierarchical Multipole Parity Limits SmallIntegral

variable {χ : ℂ → ℝ} {β lam M : ℝ}

/-! ### Measurability -/

section Meas

variable {ι β' : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype β'] [DecidableEq β']
variable {w : ℂ × ℂ → ℂ × ℂ → ℝ} {ψ : ℂ × ℂ → ℝ}

theorem measurable_stableWeight_pair (hwm : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => w q.1 q.2) :
    Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => stableWeight β w q.1 q.2 := by
  unfold stableWeight
  exact Measurable.ite measurableSet_isStableDipolePair
    (Real.measurable_exp.comp (measurable_const.mul hwm)) measurable_const

omit [Fintype ι] [DecidableEq ι] [LinearOrder ι] in
theorem measurable_stableWeight_app (hwm : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => w q.1 q.2)
    (i j : ι) : Measurable fun c : ι → ℂ × ℂ => stableWeight β w (c i) (c j) :=
  Measurable.comp (g := fun q : (ℂ × ℂ) × (ℂ × ℂ) => stableWeight β w q.1 q.2)
    (f := fun y : ι → ℂ × ℂ => (y i, y j)) (measurable_stableWeight_pair hwm)
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j))

omit [LinearOrder ι] [Fintype β'] in
theorem measurable_nearConnInd (blk : ι → β') (S : β') :
    Measurable (nearConnInd (ι := ι) M lam blk S) := by
  classical
  unfold nearConnInd
  exact Measurable.ite (measurableSet_setOf_fromRel_multipoleLinked M lam
    (fun G => (G.induce {i | blk i = S}).Connected)) measurable_const measurable_const

omit [Fintype β'] in
theorem measurable_blockWW (hwm : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => w q.1 q.2)
    (hψm : Measurable ψ) (blk : ι → β') (S : β') :
    Measurable (blockWW (ι := ι) β w ψ M lam blk S) := by
  classical
  have h1 : Measurable fun c : ι → ℂ × ℂ => ∏ i, ∏ j,
      (if blk i = S ∧ blk j = S ∧ i < j then stableWeight β w (c i) (c j) else 1) :=
    Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => by
      split_ifs
      · exact measurable_stableWeight_app hwm i j
      · exact measurable_const
  have h2 : Measurable fun c : ι → ℂ × ℂ => ∏ i, (if blk i = S then ψ (c i) else 1) :=
    Finset.measurable_prod _ fun i _ => by
      split_ifs
      · exact hψm.comp (measurable_pi_apply i)
      · exact measurable_const
  exact ((measurable_nearConnInd blk S).mul h1).mul h2

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_farBondW (hwm : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => w q.1 q.2)
    (e : Sym2 ι) : Measurable fun c : ι → ℂ × ℂ => farBondW β w M lam c e := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    simp only [farBondW, symmLift_mk, farBondWij, sOrd]
    refine Measurable.ite (measurableSet_multipoleLinked_apply M lam i j) measurable_const ?_
    split_ifs
    · exact (measurable_stableWeight_app hwm i j).sub_const 1
    · exact (measurable_stableWeight_app hwm j i).sub_const 1

theorem measurable_clusterQ (hwm : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => w q.1 q.2)
    (hψm : Measurable ψ) (blk : ι → β') (Dn Dz Df : Finset (Sym2 ι)) :
    Measurable (clusterQ (ι := ι) β w ψ M lam blk Dn Dz Df) := by
  unfold clusterQ clusterG
  refine (((Finset.measurable_prod _ fun S _ => measurable_blockWW hwm hψm blk S).mul ?_).mul ?_).mul
    (Finset.measurable_prod _ fun e _ => measurable_farBondW hwm e)
  · exact Finset.measurable_prod _ fun e _ => measurable_farInd M lam e
  · exact Finset.measurable_prod _ fun e _ => (measurable_linkIndE M lam e).neg

/-! ### A crude bound -/

theorem abs_clusterQ_le (blk : ι → β') (Dn Dz Df : Finset (Sym2 ι)) (c : ι → ℂ × ℂ)
    {W Ψ : ℝ} (hW : 1 ≤ W) (hΨ : 1 ≤ Ψ)
    (hs : ∀ i j, 0 ≤ stableWeight β w (c i) (c j) ∧ stableWeight β w (c i) (c j) ≤ W)
    (hψ : ∀ i, 0 ≤ ψ (c i) ∧ ψ (c i) ≤ Ψ) :
    |clusterQ β w ψ M lam blk Dn Dz Df c| ≤
      (W ^ (Fintype.card ι * Fintype.card ι) * Ψ ^ Fintype.card ι) ^ Fintype.card β' *
        (W + 1) ^ Df.card := by
  classical
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hΨ0 : 0 ≤ Ψ := zero_le_one.trans hΨ
  have hblock : ∀ S, |blockWW β w ψ M lam blk S c| ≤
      W ^ (Fintype.card ι * Fintype.card ι) * Ψ ^ Fintype.card ι := by
    intro S
    unfold blockWW
    rw [abs_mul, abs_mul]
    have h1 : |nearConnInd M lam blk S c| ≤ 1 := by
      unfold nearConnInd; split_ifs <;> simp
    have h2 : |∏ i, ∏ j, if blk i = S ∧ blk j = S ∧ i < j then stableWeight β w (c i) (c j)
        else 1| ≤ W ^ (Fintype.card ι * Fintype.card ι) :=
      abs_prod_prod_le _ fun i j => by
        split_ifs
        · rw [abs_of_nonneg (hs i j).1]; exact (hs i j).2
        · rw [abs_one]; exact hW
    have h3 : |∏ i, if blk i = S then ψ (c i) else 1| ≤ Ψ ^ Fintype.card ι := by
      rw [abs_prod]
      calc ∏ i, |if blk i = S then ψ (c i) else 1| ≤ ∏ _i : ι, Ψ := by
            refine prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => ?_
            split_ifs
            · rw [abs_of_nonneg (hψ i).1]; exact (hψ i).2
            · rw [abs_one]; exact hΨ
        _ = Ψ ^ Fintype.card ι := by rw [prod_const, card_univ]
    calc |nearConnInd M lam blk S c| * |∏ i, ∏ j, if blk i = S ∧ blk j = S ∧ i < j then
          stableWeight β w (c i) (c j) else 1| * |∏ i, if blk i = S then ψ (c i) else 1|
        ≤ 1 * W ^ (Fintype.card ι * Fintype.card ι) * Ψ ^ Fintype.card ι := by
          gcongr
      _ = _ := by ring
  have hbond : ∀ e, |farBondW β w M lam c e| ≤ W + 1 := by
    intro e
    induction e using Sym2.ind with
    | h i j =>
      simp only [farBondW, symmLift_mk, farBondWij, sOrd]
      split_ifs
      · rw [abs_zero]; linarith
      · rw [abs_le]; constructor <;> linarith [(hs i j).1, (hs i j).2]
      · rw [abs_le]; constructor <;> linarith [(hs j i).1, (hs j i).2]
  unfold clusterQ clusterG
  rw [abs_mul, abs_mul, abs_mul]
  have hP : |∏ S, blockWW β w ψ M lam blk S c| ≤
      (W ^ (Fintype.card ι * Fintype.card ι) * Ψ ^ Fintype.card ι) ^ Fintype.card β' := by
    rw [abs_prod]
    calc ∏ S, |blockWW β w ψ M lam blk S c| ≤
          ∏ _S : β', W ^ (Fintype.card ι * Fintype.card ι) * Ψ ^ Fintype.card ι :=
          prod_le_prod₀ (fun S _ => abs_nonneg _) fun S _ => hblock S
      _ = _ := by rw [prod_const, card_univ]
  have hF : |∏ e ∈ Df, farBondW β w M lam c e| ≤ (W + 1) ^ Df.card := by
    rw [abs_prod, ← prod_const]
    exact prod_le_prod₀ (fun e _ => abs_nonneg _) fun e _ => hbond e
  calc |∏ S, blockWW β w ψ M lam blk S c| * |∏ e ∈ Dz, farInd M lam c e| *
        |∏ e ∈ Dn, -linkIndE M lam c e| * |∏ e ∈ Df, farBondW β w M lam c e|
      ≤ (W ^ (Fintype.card ι * Fintype.card ι) * Ψ ^ Fintype.card ι) ^ Fintype.card β' * 1 * 1 *
          (W + 1) ^ Df.card := by
        gcongr
        · exact abs_prod_farInd_le Dz c
        · exact (abs_prod_linkIndE_le Dn c).trans (by split_ifs <;> norm_num)
    _ = _ := by ring

end Meas

/-! ### The indicator of `𝒟` -/

section Short

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Classical in
/-- The indicator `∏_{e ∈ Df} 𝟙_{d_e ≤ D}` of `𝒟`. -/
noncomputable def shortInd (D : ℝ) (Df : Finset (Sym2 ι)) (c : ι → ℂ × ℂ) : ℝ :=
  ∏ e ∈ Df, if distE c e ≤ D then 1 else 0

omit [Fintype ι] [DecidableEq ι] in
theorem shortInd_nonneg (D : ℝ) (Df : Finset (Sym2 ι)) (c : ι → ℂ × ℂ) :
    0 ≤ shortInd D Df c := by
  classical
  unfold shortInd
  exact prod_nonneg fun e _ => by split_ifs <;> norm_num

omit [Fintype ι] [DecidableEq ι] in
theorem shortInd_le_one (D : ℝ) (Df : Finset (Sym2 ι)) (c : ι → ℂ × ℂ) :
    shortInd D Df c ≤ 1 := by
  classical
  unfold shortInd
  exact prod_le_one₀ (fun e _ => by split_ifs <;> norm_num) fun e _ => by split_ifs <;> norm_num

theorem shortInd_eq_one_or (D : ℝ) (Df : Finset (Sym2 ι)) (c : ι → ℂ × ℂ) :
    (shortInd D Df c = 1 ∧ ∀ e ∈ Df, distE c e ≤ D) ∨
      (shortInd D Df c = 0 ∧ ∃ e ∈ Df, D < distE c e) := by
  classical
  unfold shortInd
  by_cases h : ∀ e ∈ Df, distE c e ≤ D
  · exact Or.inl ⟨prod_eq_one fun e he => by rw [ite_eq_left (h e he)], h⟩
  · push Not at h
    obtain ⟨e, he, hlt⟩ := h
    exact Or.inr ⟨prod_eq_zero he (by rw [ite_eq_right (not_le.2 hlt)]), e, he, hlt⟩

theorem dipoleDist_swap_l (d e : ℂ × ℂ) : dipoleDist d.swap e = dipoleDist d e := by
  unfold dipoleDist
  simp only [Prod.fst_swap, Prod.snd_swap]
  exact min_comm _ _

theorem dipoleDist_swap_r (d e : ℂ × ℂ) : dipoleDist d e.swap = dipoleDist d e := by
  unfold dipoleDist
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [min_comm ‖d.1 - e.2‖, min_comm ‖d.2 - e.2‖]

omit [Fintype ι] in
theorem distE_flip (B : Finset ι) (c : ι → ℂ × ℂ) (e : Sym2 ι) :
    distE (flipCfg B c) e = distE c e := by
  induction e using Sym2.ind with
  | h i j =>
    show dipoleDist (flipCfg B c i) (flipCfg B c j) = dipoleDist (c i) (c j)
    simp only [flipCfg_apply]
    split_ifs <;> simp only [dipoleDist_swap_l, dipoleDist_swap_r]

omit [Fintype ι] in
theorem shortInd_flip (D : ℝ) (Df : Finset (Sym2 ι)) (B : Finset ι) (c : ι → ℂ × ℂ) :
    shortInd D Df (flipCfg B c) = shortInd D Df c := by
  classical
  unfold shortInd
  simp_rw [distE_flip]

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_distE (e : Sym2 ι) : Measurable fun c : ι → ℂ × ℂ => distE c e := by
  induction e using Sym2.ind with
  | h i j =>
    show Measurable fun c : ι → ℂ × ℂ => dipoleDist (c i) (c j)
    unfold dipoleDist
    fun_prop

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_shortInd (D : ℝ) (Df : Finset (Sym2 ι)) :
    Measurable (shortInd (ι := ι) D Df) := by
  classical
  unfold shortInd
  exact Finset.measurable_prod _ fun e _ => Measurable.ite
    (measurableSet_le (measurable_distE e) measurable_const) measurable_const measurable_const

end Short

end ExpansionK

end MultipoleBKT

end
