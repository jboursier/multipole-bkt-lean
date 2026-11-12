/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.DiffMajorant

/-!
# Hyperbolic bond bounds and common block factors

See Lemma A.7. The even and odd bond bounds follow from the hyperbolic series.
The exact product of block weights identifies the common factors of
the five-subset expansion.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionK

open MeasureTheory Set Finset SimpleGraph
open Hierarchical Multipole Parity Limits SmallIntegral

variable {β lam M : ℝ}

/-! ### Hyperbolic estimates -/

section Hyperbolic

theorem abs_sinh_le (y : ℝ) : |Real.sinh y| ≤ |y| * Real.exp |y| := by
  have h := GeneralExpansion.abs_exp_sub_exp_le y (-y)
  have hmax : max y (-y) = |y| := (abs_eq_max_neg).symm
  rw [hmax, show y - -y = 2 * y by ring, abs_mul, abs_two] at h
  rw [Real.sinh_eq, abs_div, abs_two]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

theorem abs_sinh_sub_sinh_le (a b : ℝ) :
    |Real.sinh a - Real.sinh b| ≤ Real.exp (|a| + |b|) * |a - b| := by
  have h1 := GeneralExpansion.abs_exp_sub_exp_le a b
  have h2 := GeneralExpansion.abs_exp_sub_exp_le (-a) (-b)
  have hm1 : Real.exp (max a b) ≤ Real.exp (|a| + |b|) :=
    Real.exp_le_exp.2 (max_le (by linarith [le_abs_self a, abs_nonneg b])
      (by linarith [le_abs_self b, abs_nonneg a]))
  have hm2 : Real.exp (max (-a) (-b)) ≤ Real.exp (|a| + |b|) :=
    Real.exp_le_exp.2 (max_le (by linarith [neg_le_abs a, abs_nonneg b])
      (by linarith [neg_le_abs b, abs_nonneg a]))
  rw [show -a - -b = -(a - b) by ring, abs_neg] at h2
  rw [Real.sinh_eq, Real.sinh_eq,
    show (Real.exp a - Real.exp (-a)) / 2 - (Real.exp b - Real.exp (-b)) / 2 =
      ((Real.exp a - Real.exp b) - (Real.exp (-a) - Real.exp (-b))) / 2 by ring,
    abs_div, abs_two, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have h3 := abs_sub (Real.exp a - Real.exp b) (Real.exp (-a) - Real.exp (-b))
  have hab := abs_nonneg (a - b)
  nlinarith

theorem cosh_sub_cosh_eq (a b : ℝ) :
    Real.cosh a - Real.cosh b = 2 * Real.sinh ((a + b) / 2) * Real.sinh ((a - b) / 2) := by
  rw [Real.cosh_eq, Real.cosh_eq, Real.sinh_eq, Real.sinh_eq]
  have e1 : Real.exp ((a + b) / 2) * Real.exp ((a - b) / 2) = Real.exp a := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp ((a + b) / 2) * Real.exp (-((a - b) / 2)) = Real.exp b := by
    rw [← Real.exp_add]; ring_nf
  have e3 : Real.exp (-((a + b) / 2)) * Real.exp ((a - b) / 2) = Real.exp (-b) := by
    rw [← Real.exp_add]; ring_nf
  have e4 : Real.exp (-((a + b) / 2)) * Real.exp (-((a - b) / 2)) = Real.exp (-a) := by
    rw [← Real.exp_add]; ring_nf
  linear_combination (-1 / 2 : ℝ) * e1 + (1 / 2 : ℝ) * e2 + (1 / 2 : ℝ) * e3 +
    (-1 / 2 : ℝ) * e4

theorem abs_cosh_sub_cosh_le (a b : ℝ) :
    |Real.cosh a - Real.cosh b| ≤ (|a| + |b|) * |a - b| * Real.exp (|a| + |b|) := by
  rw [cosh_sub_cosh_eq, abs_mul, abs_mul, abs_two]
  have h1 := abs_sinh_le ((a + b) / 2)
  have h2 := abs_sinh_le ((a - b) / 2)
  have hp : |(a + b) / 2| ≤ (|a| + |b|) / 2 := by
    rw [abs_div, abs_two]
    exact div_le_div_of_nonneg_right (abs_add_le a b) (by norm_num)
  have hq : |(a - b) / 2| = |a - b| / 2 := by rw [abs_div, abs_two]
  have hpq : |(a + b) / 2| + |(a - b) / 2| ≤ |a| + |b| := by
    rw [abs_div, abs_div, abs_two]
    have := abs_add_le a b
    have := abs_sub a b
    linarith
  have hexp : Real.exp |(a + b) / 2| * Real.exp |(a - b) / 2| ≤ Real.exp (|a| + |b|) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 hpq
  have hs1 : 0 ≤ |Real.sinh ((a + b) / 2)| := abs_nonneg _
  have hs2 : 0 ≤ |Real.sinh ((a - b) / 2)| := abs_nonneg _
  calc 2 * |Real.sinh ((a + b) / 2)| * |Real.sinh ((a - b) / 2)|
      ≤ 2 * (|(a + b) / 2| * Real.exp |(a + b) / 2|) * (|(a - b) / 2| * Real.exp |(a - b) / 2|) := by
        gcongr
    _ = 2 * (|(a + b) / 2| * |(a - b) / 2|) *
        (Real.exp |(a + b) / 2| * Real.exp |(a - b) / 2|) := by ring
    _ ≤ 2 * ((|a| + |b|) / 2 * |(a - b) / 2|) * Real.exp (|a| + |b|) := by
        gcongr
    _ = 2 * ((|a| + |b|) / 2 * (|a - b| / 2)) * Real.exp (|a| + |b|) := by rw [hq]
    _ ≤ (|a| + |b|) * |a - b| * Real.exp (|a| + |b|) := by
        have : 0 ≤ (|a| + |b|) * |a - b| * Real.exp (|a| + |b|) := by positivity
        nlinarith

end Hyperbolic

/-! ### The odd and even parts of a bond -/

section Parts

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- The constant `1 + βC e^{βC} + (βC)² e^{βC}` of the bounds of the odd and even parts. -/
noncomputable def partConst (β C : ℝ) : ℝ :=
  1 + β * C * Real.exp (β * C) + (β * C) ^ 2 * Real.exp (β * C)

theorem one_le_partConst {C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C) : 1 ≤ partConst β C := by
  unfold partConst
  have : 0 ≤ β * C := mul_nonneg hβ hC
  have h1 : 0 ≤ β * C * Real.exp (β * C) := by positivity
  have h2 : 0 ≤ (β * C) ^ 2 * Real.exp (β * C) := by positivity
  linarith

omit [Fintype ι] [DecidableEq ι] in
theorem abs_wOrd_le {w : ℂ × ℂ → ℂ × ℂ → ℝ} {C : ℝ} (c : ι → ℂ × ℂ) {i j : ι}
    (hw : ∀ i j, ¬ MultipoleLinked M lam (c i) (c j) → |w (c i) (c j)| ≤ C * ahat (c i) (c j))
    (hl : ¬ MultipoleLinked M lam (c i) (c j)) : |wOrd w c i j| ≤ C * ahat (c i) (c j) := by
  unfold wOrd
  split_ifs
  · exact hw i j hl
  · rw [ahat_comm]
    exact hw j i fun h => hl (Limits.multipoleLinked_comm.1 h)

omit [Fintype ι] [DecidableEq ι] in
theorem abs_alphaW_le {w : ℂ × ℂ → ℂ × ℂ → ℝ} {C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (c : ι → ℂ × ℂ)
    (hw : ∀ i j, ¬ MultipoleLinked M lam (c i) (c j) → |w (c i) (c j)| ≤ C * ahat (c i) (c j))
    (hah : ∀ i j, ¬ MultipoleLinked M lam (c i) (c j) → ahat (c i) (c j) ≤ 1)
    {e : Sym2 ι} (he : FarE M lam c e) :
    |alphaW β w M lam c e| ≤ partConst β C * ahatE c e ^ 2 := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    have hl : ¬ MultipoleLinked M lam (c i) (c j) := he
    simp only [alphaW, symmLift_mk, ite_eq_right hl, ahatE]
    have hwo := abs_wOrd_le c hw hl
    have ha0 := ahat_nonneg (c i) (c j)
    have ha1 := hah i j hl
    have h1 := abs_cosh_sub_cosh_le (β * wOrd w c i j) 0
    rw [Real.cosh_zero, sub_zero, abs_zero, add_zero] at h1
    have hbw : |β * wOrd w c i j| ≤ β * C * ahat (c i) (c j) := by
      rw [abs_mul, abs_of_nonneg hβ, mul_assoc]
      exact mul_le_mul_of_nonneg_left hwo hβ
    have hbw1 : |β * wOrd w c i j| ≤ β * C := by
      refine hbw.trans ?_
      have : 0 ≤ β * C := mul_nonneg hβ hC
      nlinarith
    have hexp : Real.exp |β * wOrd w c i j| ≤ Real.exp (β * C) := Real.exp_le_exp.2 hbw1
    refine h1.trans ?_
    have hsq : |β * wOrd w c i j| * |β * wOrd w c i j| ≤ (β * C) ^ 2 * ahat (c i) (c j) ^ 2 := by
      have := mul_le_mul hbw hbw (abs_nonneg _) (by positivity)
      nlinarith
    unfold partConst
    have hE0 : 0 ≤ Real.exp (β * C) := (Real.exp_pos _).le
    have hBC : 0 ≤ β * C := mul_nonneg hβ hC
    calc |β * wOrd w c i j| * |β * wOrd w c i j| * Real.exp |β * wOrd w c i j|
        ≤ (β * C) ^ 2 * ahat (c i) (c j) ^ 2 * Real.exp (β * C) :=
          mul_le_mul hsq hexp (Real.exp_pos _).le (by positivity)
      _ ≤ (1 + β * C * Real.exp (β * C) + (β * C) ^ 2 * Real.exp (β * C)) *
          ahat (c i) (c j) ^ 2 := by
          have : 0 ≤ ahat (c i) (c j) ^ 2 := sq_nonneg _
          nlinarith [mul_nonneg hBC hE0]

omit [Fintype ι] [DecidableEq ι] in
theorem abs_gammaW_le {w : ℂ × ℂ → ℂ × ℂ → ℝ} {C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (c : ι → ℂ × ℂ)
    (hw : ∀ i j, ¬ MultipoleLinked M lam (c i) (c j) → |w (c i) (c j)| ≤ C * ahat (c i) (c j))
    (hah : ∀ i j, ¬ MultipoleLinked M lam (c i) (c j) → ahat (c i) (c j) ≤ 1)
    {e : Sym2 ι} (he : FarE M lam c e) :
    |gammaW β w M lam c e| ≤ partConst β C * ahatE c e := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    have hl : ¬ MultipoleLinked M lam (c i) (c j) := he
    simp only [gammaW, symmLift_mk, ite_eq_right hl, ahatE, abs_neg]
    have hwo := abs_wOrd_le c hw hl
    have ha0 := ahat_nonneg (c i) (c j)
    have ha1 := hah i j hl
    have hbw : |β * wOrd w c i j| ≤ β * C * ahat (c i) (c j) := by
      rw [abs_mul, abs_of_nonneg hβ, mul_assoc]
      exact mul_le_mul_of_nonneg_left hwo hβ
    have hBC : 0 ≤ β * C := mul_nonneg hβ hC
    have hbw1 : |β * wOrd w c i j| ≤ β * C := hbw.trans (by nlinarith)
    have hexp : Real.exp |β * wOrd w c i j| ≤ Real.exp (β * C) := Real.exp_le_exp.2 hbw1
    have hE0 : 0 ≤ Real.exp (β * C) := (Real.exp_pos _).le
    refine (abs_sinh_le _).trans ?_
    unfold partConst
    calc |β * wOrd w c i j| * Real.exp |β * wOrd w c i j|
        ≤ β * C * ahat (c i) (c j) * Real.exp (β * C) :=
          mul_le_mul hbw hexp (Real.exp_pos _).le (by positivity)
      _ ≤ (1 + β * C * Real.exp (β * C) + (β * C) ^ 2 * Real.exp (β * C)) * ahat (c i) (c j) := by
          nlinarith [mul_nonneg (sq_nonneg (β * C)) hE0, mul_nonneg ha0 hE0]

/-- The constant of the bond differences. -/
noncomputable def diffConst (β C C₂ : ℝ) : ℝ :=
  Real.exp (β * C) * β * C₂ * (1 + β * C)

end Parts

/-! ### The block weights -/

section Blocks

variable {ι β' : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype β'] [DecidableEq β']

open scoped Classical in
theorem prod_blockWW_eq (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (ψ : ℂ × ℂ → ℝ) (M lam : ℝ)
    (blk : ι → β') (c : ι → ℂ × ℂ) :
    ∏ S, blockWW β w ψ M lam blk S c = (∏ S, nearConnInd M lam blk S c) *
      ((∏ i, ∏ j, if blk i = blk j ∧ i < j then stableWeight β w (c i) (c j) else 1) *
        ∏ i, ψ (c i)) := by
  unfold blockWW
  rw [prod_mul_distrib, prod_mul_distrib, mul_assoc]
  congr 2
  · rw [prod_comm]
    refine prod_congr rfl fun i _ => ?_
    rw [prod_comm]
    refine prod_congr rfl fun j _ => ?_
    have : ∀ S : β', (if blk i = S ∧ blk j = S ∧ i < j then stableWeight β w (c i) (c j) else 1) =
        if blk i = S then (if blk j = S ∧ i < j then stableWeight β w (c i) (c j) else 1)
          else 1 := fun S => by
      by_cases h1 : blk i = S
      · rw [ite_eq_left h1]
        by_cases h2 : blk j = S ∧ i < j
        · rw [ite_eq_left ⟨h1, h2⟩, ite_eq_left h2]
        · rw [ite_eq_right (fun h => h2 h.2), ite_eq_right h2]
      · rw [ite_eq_right (fun h => h1 h.1), ite_eq_right h1]
    simp_rw [this]
    rw [prod_ite_eq univ (blk i), ite_eq_left (Finset.mem_univ _)]
    by_cases h : blk j = blk i ∧ i < j
    · rw [ite_eq_left h, ite_eq_left ⟨h.1.symm, h.2⟩]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ⟨h'.1.symm, h'.2⟩)]
  · rw [prod_comm]
    refine prod_congr rfl fun i _ => ?_
    rw [prod_ite_eq univ (blk i), ite_eq_left (Finset.mem_univ _)]

omit [LinearOrder ι] in
open scoped Classical in
theorem abs_prod_linkIndE_le (Dn : Finset (Sym2 ι)) (c : ι → ℂ × ℂ) :
    |∏ e ∈ Dn, -linkIndE M lam c e| ≤
      if ∀ i j, s(i, j) ∈ Dn → i ≠ j → MultipoleLinked M lam (c i) (c j) then 1 else 0 := by
  classical
  split_ifs with hD
  · rw [abs_prod]
    exact prod_le_one₀ (fun e _ => abs_nonneg _) fun e _ => by
      rw [abs_neg]
      induction e using Sym2.ind with
      | h i j =>
        simp only [linkIndE, symmLift_mk, linkInd]
        split_ifs <;> norm_num
  · push Not at hD
    obtain ⟨i, j, hij, -, hnl⟩ := hD
    rw [prod_eq_zero hij (by simp only [linkIndE, symmLift_mk, linkInd, ite_eq_right hnl, neg_zero]),
      abs_zero]

omit [Fintype ι] [DecidableEq ι] [LinearOrder ι] in
theorem abs_prod_farInd_le (Dz : Finset (Sym2 ι)) (c : ι → ℂ × ℂ) :
    |∏ e ∈ Dz, farInd M lam c e| ≤ 1 := by
  rw [abs_prod]
  exact prod_le_one₀ (fun e _ => abs_nonneg _) fun e _ => by
    rw [abs_of_nonneg (farInd_nonneg c e)]; exact farInd_le_one c e

end Blocks

end ExpansionK

end MultipoleBKT

end
