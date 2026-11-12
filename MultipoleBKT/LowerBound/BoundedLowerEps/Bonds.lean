/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.BoundedLowerEps.Transfer
public import MultipoleBKT.LowerBound.BoundedLowerEps.Multipole

/-!
# Pair bounds for the hatted lower activities

Proposition 4.23, (4.73). The zero models use hatted
odd and even weights. The screened minus model uses Remark 4.30 directly.
-/

@[expose] public section

namespace MultipoleBKT

namespace BoundedLowerEps

open MeasureTheory Finset SimpleGraph
open Multipole SetPartition Limits SmallIntegral Hierarchical Parity

variable {β lam M : ℝ}

/-! ### Bond majorants on pairs of dipoles -/

section Majorants

open scoped Classical in
/-- `min(1, â_ij) 𝟙_{𝓑_ij^c}` on a pair of dipoles. -/
noncomputable def oddMajP (M lam : ℝ) (d e : ℂ × ℂ) : ℝ :=
  if MultipoleLinked M lam d e then 0 else min 1 (ahat d e)

open scoped Classical in
/-- `min(1, â_ij)² 𝟙_{𝓑_ij^c} + 𝟙_{𝓑_ij}` on a pair of dipoles. -/
noncomputable def evenMajP (M lam : ℝ) (d e : ℂ × ℂ) : ℝ :=
  if MultipoleLinked M lam d e then 1 else min 1 (ahat d e) ^ 2

theorem oddMajP_comm (M lam : ℝ) (d e : ℂ × ℂ) : oddMajP M lam d e = oddMajP M lam e d := by
  classical
  unfold oddMajP
  rw [ahat_comm]
  exact if_congr Limits.multipoleLinked_comm rfl rfl

theorem evenMajP_comm (M lam : ℝ) (d e : ℂ × ℂ) : evenMajP M lam d e = evenMajP M lam e d := by
  classical
  unfold evenMajP
  rw [ahat_comm]
  exact if_congr Limits.multipoleLinked_comm rfl rfl

theorem oddMajP_nonneg (M lam : ℝ) (d e : ℂ × ℂ) : 0 ≤ oddMajP M lam d e := by
  unfold oddMajP
  split_ifs
  · exact le_rfl
  · exact le_min zero_le_one (ahat_nonneg _ _)

theorem evenMajP_nonneg (M lam : ℝ) (d e : ℂ × ℂ) : 0 ≤ evenMajP M lam d e := by
  unfold evenMajP
  split_ifs
  · exact zero_le_one
  · positivity

/-- The constant of `abs_bonds_le`. -/
noncomputable def bondConst (β Cw : ℝ) : ℝ :=
  1 + β * Cw * Real.exp (β * Cw) + (β * Cw) ^ 2 * Real.exp (β * Cw)

theorem one_le_bondConst {β Cw : ℝ} (hβ : 0 ≤ β) (hCw : 0 ≤ Cw) : 1 ≤ bondConst β Cw := by
  unfold bondConst
  have : 0 ≤ β * Cw := mul_nonneg hβ hCw
  have : 0 ≤ β * Cw * Real.exp (β * Cw) := by positivity
  have : 0 ≤ (β * Cw) ^ 2 * Real.exp (β * Cw) := by positivity
  linarith

/-- **The bond bounds** (Remark 4.30, Lemma 3.7(2)–(3)): if `|w_ij| ≤ C_w â_ij` and `â_ij ≤ 1` on
`𝓑_ij^c` (`M ≥ 1`), then `|a^w_ij 𝟙_{𝓑^c}| ≤ C oddMajP_ij` and
`|b^w_ij 𝟙_{𝓑^c} - 𝟙_𝓑| ≤ C evenMajP_ij`, `C = bondConst β C_w`. -/
theorem abs_bonds_le (hβ : 0 ≤ β) (hM : 1 ≤ M) {w : ℂ × ℂ → ℂ × ℂ → ℝ} {Cw : ℝ} (hCw : 0 ≤ Cw)
    {d e : ℂ × ℂ} (hw : ¬ MultipoleLinked M lam d e → |w d e| ≤ Cw * ahat d e)
    (hah : ¬ MultipoleLinked M lam d e → ahat d e ≤ 1) :
    |oddBondUnlinked β w M lam d e| ≤ bondConst β Cw * oddMajP M lam d e ∧
      |evenBondMult β w M lam d e| ≤ bondConst β Cw * evenMajP M lam d e := by
  classical
  have hC1 := one_le_bondConst hβ hCw
  by_cases hl : MultipoleLinked M lam d e
  · refine ⟨?_, ?_⟩
    · rw [oddBondUnlinked_of_linked hl, abs_zero]
      exact mul_nonneg (zero_le_one.trans hC1) (oddMajP_nonneg M lam d e)
    · unfold evenBondMult evenMajP
      rw [evenBondUnlinked_of_linked hl, ite_eq_left hl, ite_eq_left hl]
      simpa using hC1
  · have ha1 := hah hl
    have ha0 := ahat_nonneg d e
    have hmin : min 1 (ahat d e) = ahat d e := min_eq_right ha1
    set K₀ := β * Cw with hK₀
    have hK0 : 0 ≤ K₀ := mul_nonneg hβ hCw
    have hy : |β * w d e| ≤ K₀ * ahat d e := by
      rw [abs_mul, abs_of_nonneg hβ, hK₀, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hw hl) hβ
    have hyK : |β * w d e| ≤ K₀ := hy.trans (mul_le_of_le_one_right hK0 ha1)
    have hexp : Real.exp |β * w d e| ≤ Real.exp K₀ := Real.exp_le_exp.2 hyK
    refine ⟨?_, ?_⟩
    · rw [oddBondUnlinked_of_not_linked hM hl, abs_neg]
      unfold oddMajP
      rw [ite_eq_right hl, hmin]
      calc |Real.sinh (β * w d e)| ≤ |β * w d e| * Real.exp |β * w d e| := Parity.abs_sinh_le _
        _ ≤ (K₀ * ahat d e) * Real.exp K₀ :=
            mul_le_mul hy hexp (Real.exp_pos _).le (by positivity)
        _ = (K₀ * Real.exp K₀) * ahat d e := by ring
        _ ≤ bondConst β Cw * ahat d e := by
            refine mul_le_mul_of_nonneg_right ?_ ha0
            unfold bondConst
            rw [← hK₀]
            have : 0 ≤ K₀ ^ 2 * Real.exp K₀ := by positivity
            linarith
    · unfold evenBondMult evenMajP
      rw [evenBondUnlinked_of_not_linked hM hl, ite_eq_right hl, ite_eq_right hl, hmin,
        sub_zero]
      calc |Real.cosh (β * w d e) - 1| ≤ (β * w d e) ^ 2 * Real.exp |β * w d e| :=
            abs_cosh_sub_one_le _
        _ ≤ (K₀ * ahat d e) ^ 2 * Real.exp K₀ := by
            have hsq : (β * w d e) ^ 2 ≤ (K₀ * ahat d e) ^ 2 := by
              rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) hy 2
            exact mul_le_mul hsq hexp (Real.exp_pos _).le (sq_nonneg _)
        _ = (K₀ ^ 2 * Real.exp K₀) * ahat d e ^ 2 := by ring
        _ ≤ bondConst β Cw * ahat d e ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
            unfold bondConst
            rw [← hK₀]
            have : 0 ≤ K₀ * Real.exp K₀ := by positivity
            linarith

end Majorants

/-! ### The interactions on `𝓑^c` -/

section Interactions

variable {χ : ℂ → ℝ}

/-- `|v_ij| ≤ C â_ij` on `𝓑_ij^c` (Lemma 3.7(2), `M ≥ 1`). -/
theorem abs_dipoleInteraction_le_ahat (hχ : IsMollifier χ) :
    ∃ C, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → ∀ M : ℝ, 1 ≤ M → ∀ d e : ℂ × ℂ,
      ¬ MultipoleLinked M lam d e → |dipoleInteraction χ lam d e| ≤ C * ahat d e := by
  obtain ⟨C, hC0, hC⟩ := abs_dipoleInteraction_le hχ
  obtain ⟨Cb, -, hb⟩ := exists_bond_bounds hχ (le_refl (0 : ℝ))
  refine ⟨C, hC0.le, fun lam hlam M hM d e hnl => ?_⟩
  obtain ⟨hld, -, -, -⟩ := hb lam hlam M hM d e hnl
  have hmin : min ‖d.1 - d.2‖ ‖e.1 - e.2‖ ≤ dipoleDist d e := by
    rw [MultipoleLinked, not_le] at hnl
    refine le_trans ?_ hnl.le
    refine (min_le_min (le_max_left _ lam) (le_max_left _ lam)).trans ?_
    exact le_mul_of_one_le_left (le_min (le_max_of_le_right hlam.le) (le_max_of_le_right hlam.le))
      hM
  have := hC lam hlam d e hmin
  rw [max_eq_left hld.le] at this
  unfold ahat
  rwa [mul_div_assoc] at this

/-- `|ṽ_ij| ≤ C â_ij` on `𝓑_ij^c` for dipoles of length at most `ε₀ R` and `λ ≤ ε₀ R`
(Lemma 3.10, `M ≥ 1`). -/
theorem abs_upperBoundInteraction_le_ahat (hχ : IsMollifier χ) :
    ∃ C, 0 ≤ C ∧ ∀ lam ε₀ R : ℝ, 0 < lam → lam ≤ ε₀ * R → ∀ M : ℝ, 1 ≤ M → ∀ d e : ℂ × ℂ,
      ‖d.1 - d.2‖ ≤ ε₀ * R → ‖e.1 - e.2‖ ≤ ε₀ * R →
      ¬ MultipoleLinked M lam d e → |upperBoundInteraction χ lam ε₀ R d e| ≤ C * ahat d e := by
  obtain ⟨C₀, hC₀, h310⟩ := lemma_3_10 hχ
  obtain ⟨Cb, -, hb⟩ := exists_bond_bounds hχ (le_refl (0 : ℝ))
  refine ⟨C₀, hC₀.le, fun lam ε₀ R hlam hlR M hM d e hd he hnl => ?_⟩
  obtain ⟨hld, -, -, -⟩ := hb lam hlam M hM d e hnl
  have hmin : min ‖d.1 - d.2‖ ‖e.1 - e.2‖ ≤ dipoleDist d e := by
    rw [MultipoleLinked, not_le] at hnl
    refine le_trans ?_ hnl.le
    refine (min_le_min (le_max_left _ lam) (le_max_left _ lam)).trans ?_
    exact le_mul_of_one_le_left (le_min (le_max_of_le_right hlam.le) (le_max_of_le_right hlam.le))
      hM
  have hτd : 8 * max ‖d.2 - d.1‖ lam ≤ 8 * ε₀ * R := by
    rw [norm_sub_rev, mul_assoc]
    exact mul_le_mul_of_nonneg_left (max_le hd hlR) (by norm_num)
  have hτe : 8 * max ‖e.2 - e.1‖ lam ≤ 8 * ε₀ * R := by
    rw [norm_sub_rev, mul_assoc]
    exact mul_le_mul_of_nonneg_left (max_le he hlR) (by norm_num)
  have h2 := ((h310 lam (8 * ε₀ * R) hlam d e hτd hτe).2 hmin).1
  unfold upperBoundInteraction
  refine h2.trans ?_
  split_ifs
  · rw [max_eq_left hld.le]
    unfold ahat
    rw [mul_div_assoc]
  · exact mul_nonneg hC₀.le (ahat_nonneg _ _)

/-- `â_ij ≤ 1` on `𝓑_ij^c` (`M ≥ 1`). -/
theorem ahat_le_one_of_not_linked (hχ : IsMollifier χ) (hlam : 0 < lam) (hM : 1 ≤ M)
    {d e : ℂ × ℂ} (h : ¬ MultipoleLinked M lam d e) : ahat d e ≤ 1 := by
  obtain ⟨Cb, -, hb⟩ := exists_bond_bounds hχ (le_refl (0 : ℝ))
  exact (hb lam hlam M hM d e h).2.1

end Interactions

/-! ### Counting -/
/-! ### Vanishing partition functions -/

section Zero

variable {ρ : Measure (ℂ × ℂ)} {w : ℂ × ℂ → ℂ × ℂ → ℝ} {ψ : ℂ × ℂ → ℝ}

/-- If some `𝖬(S)`, `S ∈ X`, vanishes, the hierarchical model is the zero measure. -/
theorem modelHierarchical_eq_zero {X : Finset (Finset ℕ)} {S₀ : Finset ℕ} (hS₀ : S₀ ∈ X)
    (h0 : modelPartitionFunction ρ β w ψ M lam S₀ = 0) :
    modelHierarchical ρ β w ψ M lam X = 0 := by
  rw [modelHierarchical_eq]
  have : (fun c : X.biUnion id → ℂ × ℂ => ∏ S ∈ X, ENNReal.ofReal
      ((modelPartitionFunction ρ β w ψ M lam S)⁻¹ * hierBlockWeight β w ψ M lam X S c)) = 0 := by
    funext c
    exact prod_eq_zero hS₀ (by rw [h0, inv_zero, zero_mul, ENNReal.ofReal_zero])
  rw [this, withDensity_zero]

/-- If some `𝖬(S)`, `S ∈ X`, vanishes, `𝖪(X) = 0`. -/
theorem modelActivity_eq_zero_of_partitionFunction_eq_zero {X : Finset (Finset ℕ)}
    {S₀ : Finset ℕ} (hS₀ : S₀ ∈ X) (h0 : modelPartitionFunction ρ β w ψ M lam S₀ = 0) :
    modelActivity ρ β w ψ M lam X = 0 := by
  rw [modelActivity]
  split_ifs
  · rfl
  · rw [modelHierarchical_eq_zero hS₀ h0]
    simp

end Zero

end BoundedLowerEps

end MultipoleBKT

end
