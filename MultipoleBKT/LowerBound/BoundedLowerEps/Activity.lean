/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.BoundedLowerEps.BoxBound
public import MultipoleBKT.LowerBound.RouteBounded.Truncated
public import MultipoleBKT.LowerBound.RouteBounded.ScreenTruncated
public import MultipoleBKT.LowerBound.RouteBounded.ScreenTreeIntegral

/-!
# Grouped bounded lower activities

The proof of Proposition 4.23. Retain the grouped expansion, apply
Corollary 4.34, peel its odd components and choose a separate even tree.
Integrate the minus model with J and the truncated zero model with Ĵ.
Finally apply Lemma 4.12 and the minus-to-zero normalizer comparison.
-/

@[expose] public section

namespace MultipoleBKT

namespace BoundedLowerEps

open MeasureTheory Finset SimpleGraph Filter
open Multipole SetPartition Limits SmallIntegral Hierarchical
open TwoComponentCoulomb (box)

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ : ℝ} {X : Finset (Finset ℕ)}

/-- The model `0` with the support `Λ² ∩ {|x - y| ≤ ε₀ R̄}`. -/
theorem modelHyp_zero_cutoff (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) (hε₀ : 0 < ε₀)
    (hN : 1 ≤ N) :
    ModelHyp (cutoffDipoleMeasure χ N p₀ β lam ε₀) β (dipoleInteraction χ lam) (fun _ => 1)
      (cutoffSet N p₀ β lam ε₀) where
  isProbabilityMeasure := isProbabilityMeasure_cutoffDipoleMeasure hχ hlam β hε₀ hN
  ae_mem := ae_cutoffDipoleMeasure χ N p₀ β lam ε₀
  measurable_w := measurable_dipoleInteraction hχ hlam
  measurable_ψ := measurable_const
  nonneg_ψ := fun _ => zero_le_one
  bdd_w := by
    obtain ⟨C, hC⟩ := exists_neg_mul_dipoleInteraction_le hχ hlam β N
    exact ⟨C, fun d hd e he => hC d hd.1 e he.1⟩
  bdd_ψ := ⟨1, fun _ _ => le_rfl⟩

/-- The arithmetic of the final bound: with `C_{β,λ,ε₀} ≥ 𝒵 λ^{2-β} / 2`,
`(N C_{β,λ,ε₀})^{-k} A (C_T N λ^{(2-β)k} g) ≤ (2/𝒵)^k A C_T g / N^{k-1}`. -/
theorem scaling_le {N : ℕ} (hN : 1 ≤ N) {Cn Z : ℝ} (hlam : 0 < lam) (hZ : 0 < Z)
    (hCn : 1 / 2 * Z * lam ^ (2 - β) ≤ Cn) {k : ℕ} (hk : 1 ≤ k) {A CT g : ℝ} (hA : 0 ≤ A)
    (hCT : 0 ≤ CT) (hg : 0 ≤ g) :
    ((N : ℝ) * Cn)⁻¹ ^ k * A * (CT * N * (lam ^ ((2 - β) * (k : ℝ)) * g)) ≤
      (2 / Z) ^ k * A * CT * g / (N : ℝ) ^ (k - 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hl : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  have hD : 0 < (N : ℝ) * (1 / 2 * Z * lam ^ (2 - β)) := by positivity
  have h1 : ((N : ℝ) * Cn)⁻¹ ^ k ≤ ((N : ℝ) * (1 / 2 * Z * lam ^ (2 - β)))⁻¹ ^ k := by
    refine pow_le_pow_left₀ (inv_nonneg.2 (hD.le.trans (mul_le_mul_of_nonneg_left hCn hN0.le)))
      ?_ k
    exact inv_anti₀ hD (mul_le_mul_of_nonneg_left hCn hN0.le)
  have hrp : lam ^ ((2 - β) * (k : ℝ)) = (lam ^ (2 - β)) ^ k := by
    rw [Real.rpow_mul hlam.le, Real.rpow_natCast]
  have hlast : 0 ≤ CT * N * (lam ^ ((2 - β) * (k : ℝ)) * g) := by
    have := Real.rpow_nonneg hlam.le ((2 - β) * (k : ℝ))
    positivity
  calc ((N : ℝ) * Cn)⁻¹ ^ k * A * (CT * N * (lam ^ ((2 - β) * (k : ℝ)) * g))
      ≤ ((N : ℝ) * (1 / 2 * Z * lam ^ (2 - β)))⁻¹ ^ k * A *
          (CT * N * (lam ^ ((2 - β) * (k : ℝ)) * g)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hA) hlast
    _ = (2 / Z) ^ k * A * CT * g / (N : ℝ) ^ (k - 1) := by
        rw [hrp]
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [Nat.add_sub_cancel]
        set u := lam ^ (2 - β)
        have hu := hl.ne'
        have hn := hN0.ne'
        rw [eq_div_iff (pow_ne_zero _ hn), inv_pow, div_pow]
        have h1 : ((N : ℝ) * (1 / 2 * Z * u)) ^ (j + 1) =
            (N : ℝ) ^ (j + 1) * (Z ^ (j + 1) / 2 ^ (j + 1)) * u ^ (j + 1) := by
          rw [mul_pow, mul_pow, mul_pow, one_div, inv_pow]; ring
        rw [h1]
        have := pow_ne_zero (j + 1) hZ.ne'
        have := pow_ne_zero (j + 1) hu
        have := pow_ne_zero (j + 1) hn
        field_simp
        ring

/-- Dividing a bound on `P |𝖪|` by `P`, when `P = 0` forces `𝖪 = 0`. -/
theorem abs_le_div_of_mul_le {P K B : ℝ} (hP : 0 ≤ P) (hK : P = 0 → K = 0) (h : P * |K| ≤ B) :
    |K| ≤ B / P := by
  rcases hP.eq_or_lt with h0 | hpos
  · rw [hK h0.symm, abs_zero, ← h0, div_zero]
  · rw [le_div_iff₀ hpos, mul_comm]
    exact h

theorem nonempty_of_card (hX : IsSubpartition X) (h2 : 1 < X.card) : 0 < (X.biUnion id).card := by
  obtain ⟨S, hS⟩ := card_pos.1 (zero_lt_one.trans h2)
  obtain ⟨i, hi⟩ := hX.1 S hS
  exact card_pos.2 ⟨i, mem_biUnion.2 ⟨S, hS, hi⟩⟩

theorem lamBound_le (k : ℕ) : Appendix.lamBound ε₀ k ≤ ε₀ :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem lamBound_le_half (k : ℕ) : Appendix.lamBound ε₀ k ≤ 1 / 2 := min_le_left _ _

/-- `e^{-L |x - y|² / (ε₀ R̄)²} ≤ e^{|L|}` on the support of `μ_{β,λ,ε₀}`. -/
theorem gaussianWeight_le_exp_abs (hlam : 0 < lam) (hε₀ : 0 < ε₀) (L : ℝ) {d : ℂ × ℂ}
    (hd : d ∈ cutoffSet N p₀ β lam ε₀) : gaussianWeight p₀ β lam ε₀ L d ≤ Real.exp |L| := by
  have hR : 0 < ε₀ * truncationScale p₀ β lam := mul_pos hε₀ (Appendix.truncationScale_pos hlam)
  refine Real.exp_le_exp.2 ?_
  have h1 : ‖d.1 - d.2‖ ^ 2 / (ε₀ * truncationScale p₀ β lam) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) hd.2 2
  have h0 : 0 ≤ ‖d.1 - d.2‖ ^ 2 / (ε₀ * truncationScale p₀ β lam) ^ 2 := by positivity
  calc -L * (‖d.1 - d.2‖ ^ 2 / (ε₀ * truncationScale p₀ β lam) ^ 2)
      ≤ |L| * (‖d.1 - d.2‖ ^ 2 / (ε₀ * truncationScale p₀ β lam) ^ 2) :=
        mul_le_mul_of_nonneg_right (neg_le_abs L) h0
    _ ≤ |L| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg L)
    _ = |L| := mul_one _

/-- The constant of the final bound. -/
noncomputable def activityConst (Z Wb Ψ Cab CT : ℝ) (k : ℕ) : ℝ :=
  LowerBound.RouteBounded.parityCount k * (2 / Z) ^ k *
    (Wb ^ (k * k) * Ψ ^ k * Cab ^ (k * k)) * (2 ^ (k * k * k) * CT)

theorem activityConst_pos {Z Wb Ψ Cab CT : ℝ} (hZ : 0 < Z) (hWb : 0 < Wb) (hΨ : 0 < Ψ)
    (hCab : 0 < Cab) (hCT : 0 < CT) (k : ℕ) : 0 < activityConst Z Wb Ψ Cab CT k := by
  unfold activityConst LowerBound.RouteBounded.parityCount
  positivity

/-- Normalization after the grouped parity and separate-tree integration. -/
theorem final_scaling_le {N : ℕ} (hN : 1 ≤ N) {Cn Z : ℝ} (hlam : 0 < lam) (hZ : 0 < Z)
    (hCn : 1 / 2 * Z * lam ^ (2 - β) ≤ Cn) {k : ℕ} (hk : 1 ≤ k) {Wb Ψ Cab CT g : ℝ}
    (hWb : 0 ≤ Wb) (hΨ : 0 ≤ Ψ) (hCab : 0 ≤ Cab) (hCT : 0 ≤ CT) (hg : 0 ≤ g) :
    LowerBound.RouteBounded.parityCount k *
      (((N : ℝ) * Cn)⁻¹ ^ k * (Wb ^ (k * k) * Ψ ^ k * Cab ^ (k * k)) *
        (2 ^ (k * k * k) * (CT * N * (lam ^ ((2 - β) * (k : ℝ)) * g)))) ≤
      activityConst Z Wb Ψ Cab CT k * g / (N : ℝ) ^ (k - 1) := by
  have hA : 0 ≤ Wb ^ (k * k) * Ψ ^ k * Cab ^ (k * k) := by positivity
  have h := scaling_le (β := β) hN hlam hZ hCn hk hA
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ (k * k * k)) hCT) hg
  have hcount : 0 ≤ LowerBound.RouteBounded.parityCount k := by
    unfold LowerBound.RouteBounded.parityCount
    positivity
  have heq : 2 ^ (k * k * k) * (CT * N * (lam ^ ((2 - β) * (k : ℝ)) * g)) =
      (2 ^ (k * k * k) * CT) * N * (lam ^ ((2 - β) * (k : ℝ)) * g) := by ring
  rw [heq]
  apply (mul_le_mul_of_nonneg_left h hcount).trans_eq
  unfold activityConst
  ring

/-- If the partition function `∏_{S ∈ X} 𝖬(S)` vanishes, so does the activity. -/
theorem modelActivity_eq_zero_of_prod_eq_zero {ρ : Measure (ℂ × ℂ)} {w : ℂ × ℂ → ℂ × ℂ → ℝ}
    {ψ : ℂ × ℂ → ℝ} (h : ∏ S ∈ X, modelPartitionFunction ρ β w ψ M lam S = 0) :
    modelActivity ρ β w ψ M lam X = 0 := by
  obtain ⟨S, hS, h0⟩ := prod_eq_zero_iff.1 h
  exact modelActivity_eq_zero_of_partitionFunction_eq_zero hS h0

/-- **Proposition 4.23, eq. (4.40), for `𝖪^0_{ε₀}`** ((4.40), proof of Proposition 4.23): for `β > 2`,
`ε₀ ∈ (0, 1)`, `M ≥ 1` and `k ∈ ℕ`, there are `C > 0` and `λ₀ > 0` such that for all `p₀`,
`λ ∈ (0, λ₀)`, there is `N₀` such that for `N ≥ N₀` and every subpartition `X` with `|X| > 1` and
`|V_X| = k`, `|𝖪^0_{ε₀}(X)| ≤ C γ_{β,λ,k} / (𝖬^0_{ε₀}(X) N^{k-1})`. `C` depends on
`χ, β, M, ε₀, k`. `λ₀` depends on `χ, β, ε₀, k`. `N₀` also on `p₀, λ`. -/
theorem zeroActivity_bound (hχ : IsMollifier χ) (hβ : 2 < β) (k : ℕ) (hM : 1 ≤ M)
    (hε₀ : 0 < ε₀) (hε₁ : ε₀ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ (p₀ : ℕ) (lam : ℝ), 0 < lam → lam < lam₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Finset (Finset ℕ), IsSubpartition X → 1 < X.card →
        (X.biUnion id).card = k →
        |zeroActivity χ N p₀ β lam M ε₀ X| ≤
          C * Appendix.gammaBeta p₀ β lam k /
            (zeroPartitionFunction χ N p₀ β lam M ε₀ X * (N : ℝ) ^ (k - 1)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, one_pos, 1, one_pos, fun p₀ lam _ _ => ⟨0, fun N _ X hX h2 hV => ?_⟩⟩
    exact absurd hV (nonempty_of_card hX h2).ne'
  have hβ0 : 0 ≤ β := by linarith
  obtain ⟨CT, hCT, hTree⟩ := LowerBound.RouteBounded.exists_hatTreeIntegral_cut_le hχ hβ hM hε₀ hε₁ k
  obtain ⟨Cd, hCd0, hCd⟩ := dipoleBond_le hχ
  obtain ⟨Cw, hCw0, hCw⟩ := abs_dipoleInteraction_le_ahat hχ
  obtain ⟨lamL, hlamL, hL⟩ := lem411_lower hχ hβ hε₀
  have hZ0 : 0 < dipoleConstant χ β := dipoleConstant_pos hχ hβ
  have hWb1 : 1 ≤ Real.exp (β * Cd) := Real.one_le_exp (mul_nonneg hβ0 hCd0)
  have hCab1 : 1 ≤ bondConst β Cw := one_le_bondConst hβ0 hCw0
  refine ⟨activityConst (dipoleConstant χ β) (Real.exp (β * Cd)) 1 (bondConst β Cw) CT k,
    activityConst_pos hZ0 (Real.exp_pos _) one_pos (zero_lt_one.trans_le hCab1) hCT k,
    min lamL (Appendix.lamBound ε₀ k), lt_min hlamL (Appendix.lamBound_pos hε₀ k),
    fun p₀ lam hlam hlt => ?_⟩
  have hlamL' : lam < lamL := hlt.trans_le (min_le_left _ _)
  have hlamB : lam ≤ Appendix.lamBound ε₀ k := (hlt.trans_le (min_le_right _ _)).le
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hL p₀ lam hlam hlamL')
  refine ⟨max N₀ 1, fun N hN X hX h2 hV => ?_⟩
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hCn := hN₀ N ((le_max_left _ _).trans hN)
  have h := modelHyp_zero_cutoff (p₀ := p₀) hχ hlam β hε₀ hN1
  have hg0 := SmallIntegral.gammaBeta_nonneg hlam p₀ β k
  have hCt0 : 0 ≤ CT * N * (lam ^ ((2 - β) * (k : ℝ)) * Appendix.gammaBeta p₀ β lam k) := by
    have := Real.rpow_nonneg hlam.le ((2 - β) * (k : ℝ))
    positivity
  have hmain := LowerBound.RouteBounded.prod_mul_abs_activity_cut_le hχ hlam hε₀ hN1 hM h
    (fun d e => Parity.dipoleInteraction_swap_left d e hχ lam)
    (fun d e => Parity.dipoleInteraction_swap_right d e hχ lam) (fun _ => rfl)
    (by
      obtain ⟨C', hC'⟩ := exists_abs_dipoleInteraction_le hχ hlam N
      exact ⟨C', fun d hd e he => hC' d hd.1 e he.1⟩)
    hWb1 le_rfl hCab1
    (fun d _ e _ => by unfold stableWeight; exact hCd β hβ0 lam hlam d e)
    (fun _ _ => le_rfl)
    (fun d _ e _ => abs_bonds_le hβ0 hM hCw0 (fun hnl => hCw lam hlam M hM d e hnl)
      (fun hnl => ahat_le_one_of_not_linked hχ hlam hM hnl))
    hX h2 hCt0
    (fun Ys hYs hdisj Ta hTa Tb hTb =>
      hTree X hX h2 hV Ys hYs hdisj Ta hTa Tb hTb p₀ lam hlam hlamB N)
  rw [hV] at hmain
  have hP0 : 0 ≤ zeroPartitionFunction χ N p₀ β lam M ε₀ X :=
    prod_nonneg fun S _ => h.modelPartitionFunction_nonneg (M := M) (lam := lam) S
  have hfin := (abs_le_div_of_mul_le hP0 (fun h0 => modelActivity_eq_zero_of_prod_eq_zero h0)
    (hmain.trans (final_scaling_le hN1 hlam hZ0 hCn hk (zero_le_one.trans hWb1) zero_le_one
      (zero_le_one.trans hCab1) hCT.le hg0)))
  refine hfin.trans_eq ?_
  rw [div_div, mul_comm (zeroPartitionFunction χ N p₀ β lam M ε₀ X)]

/-- **Proposition 4.23, eq. (4.40), for `𝖪^-_{ε₀}`** ((4.40), proof of Proposition 4.23): for `β > 2`,
`ε₀ ∈ (0, 1)`, `M ≥ 1`, `L ∈ ℝ` and `k ∈ ℕ`, there are `C > 0` and `λ₀ > 0` such that for all
`p₀`, `λ ∈ (0, λ₀)`, there is `N₀` such that for `N ≥ N₀` and every subpartition `X` with
`|X| > 1` and `|V_X| = k`, `|𝖪^-_{ε₀}(X)| ≤ C γ_{β,λ,k} / (𝖬^0_{ε₀}(X) N^{k-1})`. `C` depends on
`χ, β, M, ε₀, k, L`. `λ₀` depends on `χ, β, ε₀, k`. `N₀` also on `p₀, λ`. -/
theorem minusActivity_bound (hχ : IsMollifier χ) (hβ : 2 < β) (k : ℕ) (hM : 1 ≤ M) (L : ℝ)
    (hε₀ : 0 < ε₀) (hε₁ : ε₀ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ (p₀ : ℕ) (lam : ℝ), 0 < lam → lam < lam₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Finset (Finset ℕ), IsSubpartition X → 1 < X.card →
        (X.biUnion id).card = k →
        |minusActivity χ N p₀ β lam M ε₀ L X| ≤
          C * Appendix.gammaBeta p₀ β lam k /
            (zeroPartitionFunction χ N p₀ β lam M ε₀ X * (N : ℝ) ^ (k - 1)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, one_pos, 1, one_pos, fun p₀ lam _ _ => ⟨0, fun N _ X hX h2 hV => ?_⟩⟩
    exact absurd hV (nonempty_of_card hX h2).ne'
  have hβ0 : 0 ≤ β := by linarith
  obtain ⟨CT, hCT, hTree⟩ := LowerBound.RouteBounded.exists_screenTreeIntegral_cut_le hχ hβ hM hε₀ hε₁ k
  obtain ⟨Cd, hCd0, hCd⟩ := dipoleBond_le hχ
  obtain ⟨Cab, hCab1, hCab⟩ := Parity.remark_4_30 hχ β
  obtain ⟨C₁, hC₁, h310⟩ := lemma_3_10 hχ
  have h310' : ∀ lam τ : ℝ, 0 < lam → ∀ d e : ℂ × ℂ,
      8 * max ‖d.2 - d.1‖ lam ≤ τ → 8 * max ‖e.2 - e.1‖ lam ≤ τ →
      |screenedInteraction χ lam τ d e - dipoleInteraction χ lam d e| ≤
        C₁ * (‖d.1 - d.2‖ * ‖e.1 - e.2‖) / τ ^ 2 := fun lam τ hlam d e hd he =>
    (h310 lam τ hlam d e hd he).1
  obtain ⟨Cc, hCc, hcomp⟩ := minus_zero_comparison hχ
  obtain ⟨lamL, hlamL, hL⟩ := lem411_lower hχ hβ hε₀
  have hZ0 : 0 < dipoleConstant χ β := dipoleConstant_pos hχ hβ
  set Wb := Real.exp (β * (C₁ / 64)) * Real.exp (β * Cd) with hWb
  have hWb1 : 1 ≤ Wb := one_le_mul_of_one_le_of_one_le
    (Real.one_le_exp (mul_nonneg hβ0 (by positivity))) (Real.one_le_exp (mul_nonneg hβ0 hCd0))
  have hΨ1 : 1 ≤ Real.exp |L| := Real.one_le_exp (abs_nonneg L)
  set c : ℝ := β * (Cc / 64) * (k : ℝ) ^ 2 + |L| * k with hc
  refine ⟨Real.exp c * activityConst (dipoleConstant χ β) Wb (Real.exp |L|) Cab CT k,
    mul_pos (Real.exp_pos _) (activityConst_pos hZ0 (zero_lt_one.trans_le hWb1)
      (Real.exp_pos _) (zero_lt_one.trans_le hCab1) hCT k),
    min lamL (Appendix.lamBound ε₀ k), lt_min hlamL (Appendix.lamBound_pos hε₀ k),
    fun p₀ lam hlam hlt => ?_⟩
  have hlamL' : lam < lamL := hlt.trans_le (min_le_left _ _)
  have hlamB : lam ≤ Appendix.lamBound ε₀ k := (hlt.trans_le (min_le_right _ _)).le
  have hlamR : lam ≤ ε₀ * truncationScale p₀ β lam := by
    have h1 : 1 ≤ truncationScale p₀ β lam := Appendix.one_le_truncationScale hβ hlam
      (hlamB.trans ((lamBound_le_half k).trans (by norm_num)))
    calc lam ≤ ε₀ := hlamB.trans (lamBound_le k)
      _ ≤ ε₀ * truncationScale p₀ β lam := le_mul_of_one_le_right hε₀.le h1
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hL p₀ lam hlam hlamL')
  refine ⟨max N₀ 1, fun N hN X hX h2 hV => ?_⟩
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hCn := hN₀ N ((le_max_left _ _).trans hN)
  have h := modelHyp_minus (p₀ := p₀) hχ hlam β hε₀ hN1 hlamR L
  have hg0 := SmallIntegral.gammaBeta_nonneg hlam p₀ β k
  have hCt0 : 0 ≤ CT * N * (lam ^ ((2 - β) * (k : ℝ)) * Appendix.gammaBeta p₀ β lam k) := by
    have := Real.rpow_nonneg hlam.le ((2 - β) * (k : ℝ))
    positivity
  have hmain := LowerBound.RouteBounded.prod_mul_abs_activity_screen_cut_le hχ hlam hε₀ hN1 hM h
    (fun d e => Parity.upperBoundInteraction_swap_left d e χ lam ε₀ _)
    (fun d e => Parity.upperBoundInteraction_swap_right d e χ lam ε₀ _)
    (gaussianWeight_swap p₀ β lam ε₀ L)
    (exists_abs_upperBoundInteraction_le hχ hlam hlamR)
    hWb1 hΨ1 hCab1
    (fun d hd e he => by
      refine ((stableWeight_comparison hβ0 hC₁ h310' hlam hlamR hd.2 he.2).1).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      unfold stableWeight
      exact hCd β hβ0 lam hlam d e)
    (fun d hd => gaussianWeight_le_exp_abs hlam hε₀ L hd)
    (fun d hd e he => by
      have hb := hCab lam ε₀ (truncationScale p₀ β lam) M hlam hlamR hM d e
        (max_le hd.2 he.2)
      exact ⟨hb.1, LowerBound.RouteBounded.evenMult_le_absEven hb.2.2⟩)
    hX h2 hCt0
    (fun Ys hYs hdisj Ta hTa Tb hTb =>
      hTree X hX h2 hV Ys hYs hdisj Ta hTa Tb hTb p₀ lam hlam hlamB N)
  rw [hV] at hmain
  have hbound := hmain.trans (final_scaling_le hN1 hlam hZ0 hCn hk (zero_le_one.trans hWb1)
    (zero_le_one.trans hΨ1) (zero_le_one.trans hCab1) hCT.le hg0)
  -- compare the partition functions of the models `-` and `0`
  have hm : ∑ S ∈ X, (S.card : ℝ) = k := by
    rw [← hV, ← sum_card_eq hX]
    push_cast
    rfl
  obtain ⟨hlow, hup⟩ := hcomp N p₀ β lam M ε₀ L hβ0 hlam hε₀ hN1 hlamR X
  rw [hm, ← hc] at hlow hup
  have hPm0 : 0 ≤ minusPartitionFunction χ N p₀ β lam M ε₀ L X :=
    prod_nonneg fun S _ => h.modelPartitionFunction_nonneg (M := M) (lam := lam) S
  have hP0 : 0 ≤ zeroPartitionFunction χ N p₀ β lam M ε₀ X :=
    prod_nonneg fun S _ =>
      (modelHyp_zero (p₀ := p₀) hχ hlam β hε₀ hN1).modelPartitionFunction_nonneg
      (M := M) (lam := lam) S
  have hP0m : zeroPartitionFunction χ N p₀ β lam M ε₀ X ≤
      Real.exp c * minusPartitionFunction χ N p₀ β lam M ε₀ L X := by
    have e : Real.exp c * Real.exp (-c) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    calc zeroPartitionFunction χ N p₀ β lam M ε₀ X
        = Real.exp c * (Real.exp (-c) * zeroPartitionFunction χ N p₀ β lam M ε₀ X) := by
          rw [← mul_assoc, e, one_mul]
      _ ≤ Real.exp c * minusPartitionFunction χ N p₀ β lam M ε₀ L X :=
          mul_le_mul_of_nonneg_left hlow (Real.exp_pos c).le
  have hKz : zeroPartitionFunction χ N p₀ β lam M ε₀ X = 0 →
      minusActivity χ N p₀ β lam M ε₀ L X = 0 := by
    intro h0
    refine modelActivity_eq_zero_of_prod_eq_zero ?_
    show minusPartitionFunction χ N p₀ β lam M ε₀ L X = 0
    refine le_antisymm ?_ hPm0
    have := hup
    rwa [h0, mul_zero] at this
  have hprod : zeroPartitionFunction χ N p₀ β lam M ε₀ X * |minusActivity χ N p₀ β lam M ε₀ L X| ≤
      Real.exp c * (activityConst (dipoleConstant χ β) Wb (Real.exp |L|) Cab CT k *
        Appendix.gammaBeta p₀ β lam k / (N : ℝ) ^ (k - 1)) :=
    calc zeroPartitionFunction χ N p₀ β lam M ε₀ X * |minusActivity χ N p₀ β lam M ε₀ L X|
        ≤ Real.exp c * minusPartitionFunction χ N p₀ β lam M ε₀ L X *
            |minusActivity χ N p₀ β lam M ε₀ L X| :=
          mul_le_mul_of_nonneg_right hP0m (abs_nonneg _)
      _ = Real.exp c * (minusPartitionFunction χ N p₀ β lam M ε₀ L X *
            |minusActivity χ N p₀ β lam M ε₀ L X|) := mul_assoc _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hbound (Real.exp_pos c).le
  refine (abs_le_div_of_mul_le hP0 hKz hprod).trans_eq ?_
  rw [mul_div_assoc', div_div, mul_comm (zeroPartitionFunction χ N p₀ β lam M ε₀ X), ← mul_assoc]

end BoundedLowerEps

end MultipoleBKT

end
