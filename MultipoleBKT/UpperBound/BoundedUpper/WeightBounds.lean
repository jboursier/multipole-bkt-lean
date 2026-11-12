/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.External
public import MultipoleBKT.UpperBound.Quadratic.WeightBounds
public import MultipoleBKT.LowerBound.Parity.MayerBond

/-!
# The weight bounds on the support of `𝖯^{+,ε₀,Z}_X` (Remark 5.22, the bond bound)

The paper: Remark 5.22 (Remark 5.22, eqs.
(5.72), (5.73)) for the model with frozen bad points: the dipoles are good dipoles
`d, e ∈ I_good^Z` with `r ≤ ε₀ R̄` (the support of `𝖯^{+,ε₀,Z}_X`, `ae_plusModel`), `v^Z` is
`interactionGoodZ` (radii `τ^Z`), and the bad points are frozen. The proof of Proposition 5.18
uses these bounds on that support, and the bound
`e^{-β v^Z_ij} 𝟙_{𝒜_ij} ≤ C` on the intra-block Boltzmann factors of the density of
`𝖯^{+,ε₀,Z}_X` (the paper uses that on `𝒜_ij` the interaction
`w_ij` is bounded from below).

* `abs_interactionGoodZ_le_absOdd`: on `𝓑_de^c`, `|v^Z(d, e)| ≤ C₀ a^abs_de` and `a^abs_de ≤ 1`;
* `bornesabZ_Z`: **eq. (5.73)**: `|a^{v^Z}_de 𝟙_{𝓑^c}| ≤ C a^abs_de` and
  `|b^{v^Z}_de 𝟙_{𝓑^c} - 𝟙_𝓑| ≤ C b^abs_de` (`Parity.oddBondUnlinked`, `Parity.evenBondMult`);
* `bornesabinfty_Z`: **eq. (5.72)**: with `S_e = ∑_{j ∈ V} v^Z(e, Z_j)`,
  `|sinh(β S_e)| ≤ C r_e / d_{e,bad}` and `cosh(β S_e) ≤ C`;
* `stableWeightZ_le`: **the bond bound** `e^{-β v^Z(d, e)} 𝟙_{𝒜} ≤ C`, from Lemma 3.9 (3)
  (`|v^Z - v| ≤ C r_d r_e / max(τ_d, τ_e)² ≤ 16 C`) and the bond bound for `v` (Lemma 3.7);
* `unlinkedBondOf_eq_add`: the bond `e^{-β w} 𝟙_{𝒜} 𝟙_{𝓑^c} - 1` is
  `a^w 𝟙_{𝓑^c} + (b^w 𝟙_{𝓑^c} - 𝟙_𝓑)` (`M ≥ 1`).
-/

@[expose] public section

open Finset
open MultipoleBKT.TheoremTwo

namespace MultipoleBKT

namespace UpperBound

namespace BoundedUpper

open Hierarchical Parity Quadratic

variable {χ : ℂ → ℝ}

/-- The support of `𝖯^{+,ε₀,Z}`: a dipole of `Λ²` with `r ≤ ε₀ R̄` in `I_good^Z`. -/
def OnSupportZ {N : ℕ} (p₀ : ℕ) (β lam M ε₀ : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ)
    (e : ℂ × ℂ) : Prop :=
  e ∈ supportSet N p₀ β lam ε₀ ∧ IsGoodZ p₀ β lam M ε₀ V Z e

theorem OnSupportZ.norm_le {N : ℕ} {p₀ : ℕ} {β lam M ε₀ : ℝ} {V : Finset (Fin N)}
    {Z : Fin N → ℂ × ℂ} {e : ℂ × ℂ} (h : OnSupportZ p₀ β lam M ε₀ V Z e) :
    ‖e.1 - e.2‖ ≤ ε₀ * truncationScale p₀ β lam :=
  h.1.2

/-- The two-dipole radii `(τ_d^Z, τ_e^Z)`. -/
noncomputable abbrev pairRadii {N : ℕ} (p₀ : ℕ) (β lam ε₀ : ℝ) (V : Finset (Fin N))
    (Z : Fin N → ℂ × ℂ) (d e : ℂ × ℂ) : Fin 2 → ℝ :=
  ![goodRadiusZ p₀ β lam ε₀ V Z d, goodRadiusZ p₀ β lam ε₀ V Z e]

theorem interactionGoodZ_eq_ballGrowth {N : ℕ} (χ : ℂ → ℝ) (p₀ : ℕ) (β lam ε₀ : ℝ)
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (d e : ℂ × ℂ) :
    interactionGoodZ χ p₀ β lam ε₀ V Z d e =
      ballGrowthInteraction χ lam (pairRadii p₀ β lam ε₀ V Z d e) (pairRadii p₀ β lam ε₀ V Z d e)
        (pairConfig d e) 0 1 :=
  pairInteraction_eq_ballGrowthInteraction χ lam d e _ _

/-- **Eq. (5.73) for the weight**: on `𝓑_de^c`, `|v^Z(d, e)| ≤ C₀ a^abs_de`, and
`a^abs_de ≤ 1`, for good dipoles `d, e` on the support. -/
theorem abs_interactionGoodZ_le_absOdd (hχ : IsMollifier χ) : ∃ C₀ > 0,
    ∀ {N : ℕ} (p₀ : ℕ) (β lam M ε₀ : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), 0 < lam →
      lam ≤ ε₀ * truncationScale p₀ β lam → (3 : ℝ) ^ pBeta p₀ β ≤ M →
      V ⊆ badPointsOn p₀ β lam M ε₀ V Z → ∀ d e : ℂ × ℂ,
      OnSupportZ p₀ β lam M ε₀ V Z d → OnSupportZ p₀ β lam M ε₀ V Z e →
      ¬ MultipoleLinked M lam d e →
        |interactionGoodZ χ p₀ β lam ε₀ V Z d e| ≤
            C₀ * absOddWeight M lam ε₀ (truncationScale p₀ β lam) d e ∧
          absOddWeight M lam ε₀ (truncationScale p₀ β lam) d e ≤ 1 := by
  obtain ⟨C₀, hC₀, h39⟩ := lemma_3_9_3 hχ
  refine ⟨C₀, hC₀, fun p₀ β lam M ε₀ V Z hlam hlamh hM hVZ d e hd he h => ?_⟩
  set R := truncationScale p₀ β lam
  set τ := pairRadii p₀ β lam ε₀ V Z d e
  have hM1 : 1 ≤ M := (one_le_pow₀ (by norm_num)).trans hM
  obtain ⟨hDlam, hminD⟩ := lt_dipoleDist_of_not_linked hlam hM1 h
  have hτd : ‖d.1 - d.2‖ / 4 ≤ goodRadiusZ p₀ β lam ε₀ V Z d :=
    div_four_le_goodRadiusZ hlam hlamh hM hVZ hd.2 hd.norm_le
  have hτe : ‖e.1 - e.2‖ / 4 ≤ goodRadiusZ p₀ β lam ε₀ V Z e :=
    div_four_le_goodRadiusZ hlam hlamh hM hVZ he.2 he.norm_le
  have hl0 : lam ≤ τ 0 := lam_le_goodRadiusZ d
  have hl1 : lam ≤ τ 1 := lam_le_goodRadiusZ e
  have hτ0 : τ 0 = goodRadiusZ p₀ β lam ε₀ V Z d := rfl
  have hτ1 : τ 1 = goodRadiusZ p₀ β lam ε₀ V Z e := rfl
  have hc0 : pairConfig d e 0 = d := rfl
  have hc1 : pairConfig d e 1 = e := rfl
  have hri : ‖(pairConfig d e 0).1 - (pairConfig d e 0).2‖ ≤ 2 * (τ 0 + τ 0) := by
    rw [hc0, hτ0]
    linarith
  have hrj : ‖(pairConfig d e 1).1 - (pairConfig d e 1).2‖ ≤ 2 * (τ 1 + τ 1) := by
    rw [hc1, hτ1]
    linarith
  have hv := ((h39 lam τ τ (pairConfig d e) 0 1 hlam hl0 rfl hl1 rfl).2 hri hrj
    (by rw [hc0, hc1]; exact hminD)).1
  rw [← interactionGoodZ_eq_ballGrowth, hc0, hc1] at hv
  set D := dipoleDist d e with hDdef
  set ri := ‖d.1 - d.2‖
  set rj := ‖e.1 - e.2‖
  set Y := max D (max ri rj) with hYdef
  have hD0 : 0 < D := hlam.trans hDlam
  have hY : 0 < Y := hD0.trans_le (le_max_left _ _)
  have hXD : max D lam = D := max_eq_left hDlam.le
  rw [hXD] at hv
  have hrr : ri * rj ≤ D * Y := by
    rw [← min_mul_max]
    exact mul_le_mul hminD (le_max_right _ _) (by positivity) hD0.le
  have hcut : τ 0 + τ 1 ≤ 17 * ε₀ * R := by
    have h1 := goodRadiusZ_le (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) (V := V) (Z := Z) d
    have h2 := goodRadiusZ_le (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) (V := V) (Z := Z) e
    rw [max_eq_left hlamh] at h1 h2
    have hR : 0 ≤ ε₀ * R := hlam.le.trans hlamh
    rw [hτ0, hτ1]
    linarith
  unfold absOddWeight
  rw [ite_eq_right h, mul_one]
  refine ⟨?_, ?_⟩
  · by_cases hnear : D ≤ τ 0 + τ 1
    · rw [ite_eq_left hnear] at hv
      rw [ite_eq_left (hnear.trans hcut), mul_one, mul_div_assoc]
      refine hv.trans (le_of_eq ?_)
      simp only [Y, ri, rj]
      ring
    · rw [ite_eq_right hnear] at hv
      refine hv.trans ?_
      have : 0 ≤ ri * rj / (D * Y) * (if D ≤ 17 * ε₀ * R then (1 : ℝ) else 0) := by
        refine mul_nonneg (by positivity) ?_
        split_ifs <;> norm_num
      exact mul_nonneg hC₀.le this
  · have hA1 : ri * rj / (D * Y) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact hrr
    split_ifs
    · rw [mul_one]
      exact hA1
    · rw [mul_zero]
      exact zero_le_one

/-- **Eq. (5.73)** on the support of `𝖯^{+,ε₀,Z}` (Remark 5.22): there is
`C ≥ 1` depending only on `β` and `χ` such that `|a^{v^Z}_de 𝟙_{𝓑_de^c}| ≤ C a^abs_de` and
`|b^{v^Z}_de 𝟙_{𝓑_de^c} - 𝟙_{𝓑_de}| ≤ C b^abs_de`. -/
theorem bornesabZ_Z (hχ : IsMollifier χ) (β : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ {N : ℕ} (p₀ : ℕ) (lam M ε₀ : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), 0 < lam →
      lam ≤ ε₀ * truncationScale p₀ β lam → (3 : ℝ) ^ pBeta p₀ β ≤ M →
      V ⊆ badPointsOn p₀ β lam M ε₀ V Z → ∀ d e : ℂ × ℂ,
      OnSupportZ p₀ β lam M ε₀ V Z d → OnSupportZ p₀ β lam M ε₀ V Z e →
        |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam d e| ≤
            C * absOddWeight M lam ε₀ (truncationScale p₀ β lam) d e ∧
          |evenBondMult β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam d e| ≤
            C * absEvenWeight M lam ε₀ (truncationScale p₀ β lam) d e := by
  obtain ⟨C₀, hC₀, hv⟩ := abs_interactionGoodZ_le_absOdd hχ
  set C := 1 + |β| * C₀ * Real.exp (|β| * C₀) + (|β| * C₀) ^ 2 * Real.exp (|β| * C₀) with hC
  have hC1 : 1 ≤ C := by
    have : 0 ≤ |β| * C₀ * Real.exp (|β| * C₀) + (|β| * C₀) ^ 2 * Real.exp (|β| * C₀) := by
      positivity
    linarith
  refine ⟨C, hC1, fun p₀ lam M ε₀ V Z hlam hlamh hM hVZ d e hd he => ?_⟩
  have hM1 : 1 ≤ M := (one_le_pow₀ (by norm_num)).trans hM
  have hA := absOddWeight_nonneg M lam ε₀ (truncationScale p₀ β lam) d e
  by_cases h : MultipoleLinked M lam d e
  · rw [oddBondUnlinked_of_linked h, abs_zero]
    refine ⟨mul_nonneg (by linarith) hA, ?_⟩
    unfold evenBondMult absEvenWeight
    rw [evenBondUnlinked_of_linked h, ite_eq_left h]
    have : 0 ≤ absOddWeight M lam ε₀ (truncationScale p₀ β lam) d e ^ 2 := sq_nonneg _
    norm_num
    nlinarith
  · obtain ⟨hvde, hA1⟩ := hv p₀ β lam M ε₀ V Z hlam hlamh hM hVZ d e hd he h
    obtain ⟨h1, h2⟩ := abs_sinh_cosh_le (β := β) hC₀.le hA hA1 hvde
    rw [oddBondUnlinked_of_not_linked hM1 h, abs_neg]
    refine ⟨h1, ?_⟩
    unfold evenBondMult absEvenWeight
    rw [evenBondUnlinked_of_not_linked hM1 h, ite_eq_right h, sub_zero, add_zero]
    exact h2

/-- **Eq. (5.72)** on the support of `𝖯^{+,ε₀,Z}` (Remark 5.22): with
`S_e = ∑_{j ∈ V} v^Z(e, Z_j)`, `|a^{v^Z}_{e∞}| = |sinh(β S_e)| ≤ C r_e / d_{e,bad}` and
`1 + b^{v^Z}_{e∞} = cosh(β S_e) ≤ C`. -/
theorem bornesabinfty_Z (hχ : IsMollifier χ) (p₀ : ℕ) (β : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ {N : ℕ} (lam M ε₀ : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), 0 < lam →
      lam ≤ ε₀ * truncationScale p₀ β lam → (3 : ℝ) ^ pBeta p₀ β ≤ M → 3 ≤ M →
      V ⊆ badPointsOn p₀ β lam M ε₀ V Z → ∀ e : ℂ × ℂ, OnSupportZ p₀ β lam M ε₀ V Z e →
        |Real.sinh (β * ∑ j ∈ V, interactionExtZ χ p₀ β lam ε₀ V Z e j)| ≤
            C * (‖e.1 - e.2‖ / badDistZ p₀ β lam ε₀ V Z e) ∧
          Real.cosh (β * ∑ j ∈ V, interactionExtZ χ p₀ β lam ε₀ V Z e j) ≤ C := by
  obtain ⟨C₁, hC₁, hgb⟩ := sum_abs_interactionExtZ_le hχ p₀ β
  set C := 1 + |β| * C₁ * Real.exp (|β| * C₁) + (|β| * C₁) ^ 2 * Real.exp (|β| * C₁) with hC
  have hC1 : 1 ≤ C := by
    have : 0 ≤ |β| * C₁ * Real.exp (|β| * C₁) + (|β| * C₁) ^ 2 * Real.exp (|β| * C₁) := by
      positivity
    linarith
  refine ⟨2 * C, by linarith, fun lam M ε₀ V Z hlam hlamh hM hM3 hVZ e he => ?_⟩
  set D := badDistZ p₀ β lam ε₀ V Z e
  set S := ∑ j ∈ V, interactionExtZ χ p₀ β lam ε₀ V Z e j
  have hrD := norm_le_badDistZ hlam hlamh hM hVZ he.2 he.norm_le
  have hD : 0 < D := hlam.trans_le (lam_le_badDistZ hlam hlamh hM hVZ he.2 he.norm_le)
  have ha0 : 0 ≤ ‖e.1 - e.2‖ / D := div_nonneg (norm_nonneg _) hD.le
  have ha1 : ‖e.1 - e.2‖ / D ≤ 1 := by rwa [div_le_one hD]
  have hS : |S| ≤ C₁ * (‖e.1 - e.2‖ / D) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [← mul_div_assoc]
    exact hgb lam M ε₀ V Z hlam hlamh hM hM3 hVZ e he.2 he.norm_le
  obtain ⟨h1, h2⟩ := abs_sinh_cosh_le hC₁.le ha0 ha1 hS (β := β)
  refine ⟨h1.trans (mul_le_mul_of_nonneg_right (by linarith) ha0), ?_⟩
  have h3 : Real.cosh (β * S) - 1 ≤ C := by
    refine (le_abs_self _).trans (h2.trans ?_)
    have : (‖e.1 - e.2‖ / D) ^ 2 ≤ 1 := pow_le_one₀ ha0 ha1
    nlinarith
  linarith

/-- **The bond bound for `v^Z`**: `e^{-β v^Z(d, e)} 𝟙_{𝒜_de} ≤ C` for good dipoles on the support
(`β ≥ 0`). -/
theorem stableWeightZ_le (hχ : IsMollifier χ) (β : ℝ) (hβ : 0 ≤ β) : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} (p₀ : ℕ) (lam M ε₀ : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), 0 < lam →
      lam ≤ ε₀ * truncationScale p₀ β lam → (3 : ℝ) ^ pBeta p₀ β ≤ M →
      V ⊆ badPointsOn p₀ β lam M ε₀ V Z → ∀ d e : ℂ × ℂ,
      OnSupportZ p₀ β lam M ε₀ V Z d → OnSupportZ p₀ β lam M ε₀ V Z e →
        stableWeight β (interactionGoodZ χ p₀ β lam ε₀ V Z) d e ≤ C := by
  obtain ⟨Cb, hCb0, hCb⟩ := neg_le_dipoleInteraction hχ
  obtain ⟨C₀, hC₀, h39⟩ := lemma_3_9_3 hχ
  refine ⟨Real.exp (β * (Cb + 16 * C₀)), Real.exp_pos _,
    fun p₀ lam M ε₀ V Z hlam hlamh hM hVZ d e hd he => ?_⟩
  unfold stableWeight
  split_ifs with hA
  · refine Real.exp_le_exp.2 ?_
    set τ := pairRadii p₀ β lam ε₀ V Z d e
    have hτd : ‖d.1 - d.2‖ / 4 ≤ goodRadiusZ p₀ β lam ε₀ V Z d :=
      div_four_le_goodRadiusZ hlam hlamh hM hVZ hd.2 hd.norm_le
    have hτe : ‖e.1 - e.2‖ / 4 ≤ goodRadiusZ p₀ β lam ε₀ V Z e :=
      div_four_le_goodRadiusZ hlam hlamh hM hVZ he.2 he.norm_le
    have hl0 : lam ≤ τ 0 := lam_le_goodRadiusZ d
    have hl1 : lam ≤ τ 1 := lam_le_goodRadiusZ e
    have hτ0 : τ 0 = goodRadiusZ p₀ β lam ε₀ V Z d := rfl
    have hτ1 : τ 1 = goodRadiusZ p₀ β lam ε₀ V Z e := rfl
    have hc0 : pairConfig d e 0 = d := rfl
    have hc1 : pairConfig d e 1 = e := rfl
    have hdiff := (h39 lam τ τ (pairConfig d e) 0 1 hlam hl0 rfl hl1 rfl).1
    rw [← interactionGoodZ_eq_ballGrowth, hc0, hc1] at hdiff
    have hτpos : 0 < max (τ 0) (τ 1) := lt_max_of_lt_left (hlam.trans_le hl0)
    have hq : ‖d.1 - d.2‖ * ‖e.1 - e.2‖ / max (τ 0) (τ 1) ^ 2 ≤ 16 := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : ‖d.1 - d.2‖ ≤ 4 * max (τ 0) (τ 1) := by
        have : τ 0 ≤ max (τ 0) (τ 1) := le_max_left _ _
        have h' : ‖d.1 - d.2‖ / 4 ≤ τ 0 := by rw [hτ0]; exact hτd
        linarith
      have h2 : ‖e.1 - e.2‖ ≤ 4 * max (τ 0) (τ 1) := by
        have : τ 1 ≤ max (τ 0) (τ 1) := le_max_right _ _
        have h' : ‖e.1 - e.2‖ / 4 ≤ τ 1 := by rw [hτ1]; exact hτe
        linarith
      have := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      nlinarith
    have hv : -dipoleInteraction χ lam d e ≤ Cb := by
      have := hCb lam hlam d e hA
      linarith
    have hvZ : -interactionGoodZ χ p₀ β lam ε₀ V Z d e ≤ Cb + 16 * C₀ := by
      have h1 := (abs_le.1 hdiff).1
      rw [mul_div_assoc] at h1
      have h2 : C₀ * (‖d.1 - d.2‖ * ‖e.1 - e.2‖ / max (τ 0) (τ 1) ^ 2) ≤ C₀ * 16 :=
        mul_le_mul_of_nonneg_left hq hC₀.le
      linarith
    calc -β * interactionGoodZ χ p₀ β lam ε₀ V Z d e
        = β * -interactionGoodZ χ p₀ β lam ε₀ V Z d e := by ring
      _ ≤ β * (Cb + 16 * C₀) := mul_le_mul_of_nonneg_left hvZ hβ
  · exact (Real.exp_pos _).le

open scoped Classical in
/-- The bond `u = e^{-β w} 𝟙_{𝒜} 𝟙_{𝓑^c} - 1` of the compact form of the activity is
`a^w 𝟙_{𝓑^c} + (b^w 𝟙_{𝓑^c} - 𝟙_𝓑)` (`M ≥ 1`). -/
theorem unlinkedBondOf_eq_add {β M lam : ℝ} (hM : 1 ≤ M) (w : ℂ × ℂ → ℂ × ℂ → ℝ)
    (d e : ℂ × ℂ) :
    unlinkedBondOf β w M lam d e = oddBondUnlinked β w M lam d e + evenBondMult β w M lam d e := by
  unfold unlinkedBondOf evenBondMult stableWeight
  by_cases h : MultipoleLinked M lam d e
  · rw [ite_eq_left h, oddBondUnlinked_of_linked h, evenBondUnlinked_of_linked h, ite_eq_left h]
    ring
  · rw [ite_eq_right h, oddBondUnlinked_of_not_linked hM h, evenBondUnlinked_of_not_linked hM h,
      ite_eq_right h, ite_eq_left (remark_4_6 hM h), neg_mul, ← Real.cosh_sub_sinh]
    ring

end BoundedUpper

end UpperBound

end MultipoleBKT

end
