/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.ExpansionPlus.ExternalGain
public import MultipoleBKT.Appendix.MultipoleIntegralZ.Gate
public import MultipoleBKT.UpperBound.BoundedUpper.Inputs
public import MultipoleBKT.Main.TheoremTwo.Parameters

/-!
# Proposition 5.19, eq. (5.68) for `𝖬^{+,Z}_{ε₀}` and `𝖬̂^{+,Z}_{ε₀}`; eq. (5.105)

The paper: Proposition 5.19,
eq. (5.68) and the following sentence for `𝖬̂^{+,Z}_{ε₀}`; proof.

* `eq_M_plus_diff`: **eq. (5.68)** for `𝖬^{+,Z}_{ε₀}` and `𝖬̂^{+,Z}_{ε₀}`, against `𝖬^0_{ε₀}`
  as stated (the comparison is made at the same cutoff, see
  `MultipoleBKT.UpperBound.ExpansionPlus.MultipoleDiff`), with the constant `C` of the term
  `ε₀^{α(β)|S|} |V_bad| / N` independent of `ε₀`;
* `external_factor_bound`: **eq. (5.105)**,
  `0 ≤ g^Z_{ε₀}(S) - 1 ≤ C θ_{|S|} λ^{-2(|S|-1)}`, from `0 ≤ 𝖬^{+,Z}_{ε₀}(S)(g^Z_{ε₀}(S) - 1) ≤
  C θ_{|S|} / N^{|S|-1}` and eq. (5.65) with a constant independent of `ε₀`
  (`MultipoleBKT.plusPartitionFunction_two_sided`).

Here `θ_s = C_{ε₀} R̄^{-2} + C ε₀^{α(β)s} |V_bad|/N` (proof of Proposition 5.19).
-/

@[expose] public section

namespace MultipoleBKT

namespace UpperBound

namespace ExpansionPlus

open MeasureTheory Set Finset
open Hierarchical GeneralExpansion BoundedUpper

variable {χ : ℂ → ℝ} {β M : ℝ}

/-- `(a N + b) / N^k = (a + b/N) / N^{k-1}` for `N > 0`, `k ≥ 1`. -/
theorem div_pow_eq_div_pow_pred {N a b : ℝ} (hN : 0 < N) {k : ℕ} (hk : 1 ≤ k) :
    (a * N + b) / N ^ k = (a + b / N) / N ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]
  field_simp

/-- The scaled form of `plusPartitionFunction_mul_external_le`: if `C_{β,λ,ε₀} ≥ 𝒵_β λ^{2-β}/2`,
then `𝖬^{+,Z}_{ε₀}(S)(g^Z_{ε₀}(S) - 1) ≤ (2/𝒵)^k (C₁ ε₀^{σk-2} R̄^{-2} + C₂ ε₀^{α(β)k} |V|/N) / N^{k-1}`
(the arithmetic). -/
theorem scaled_external_le {N : ℕ} (hN : 1 ≤ N) {lam Cn Zc C₁ C₂ e₁ e₂ R v Q : ℝ}
    (hlam : 0 < lam) (hZ : 0 < Zc) (hCn : 1 / 2 * Zc * lam ^ (2 - β) ≤ Cn) (hC₁ : 0 ≤ C₁)
    (hC₂ : 0 ≤ C₂) (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂) (hR : 0 ≤ R) (hv : 0 ≤ v) {k : ℕ} (hk : 1 ≤ k)
    (hQ : Q ≤ ((N : ℝ) * Cn)⁻¹ ^ k *
      (C₁ * e₁ * N * (lam ^ ((2 - β) * k) * R) + C₂ * e₂ * v * lam ^ ((2 - β) * k))) :
    Q ≤ ((2 / Zc) ^ k * C₁ * e₁ * R + (2 / Zc) ^ k * C₂ * e₂ * (v / N)) / (N : ℝ) ^ (k - 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hX : 0 ≤ C₁ * e₁ * R * N + C₂ * e₂ * v := by positivity
  have h := normalization_scaling_le (β := β) hNpos hlam hZ hCn hX k
  have e : ((N : ℝ) * Cn)⁻¹ ^ k *
      (C₁ * e₁ * N * (lam ^ ((2 - β) * k) * R) + C₂ * e₂ * v * lam ^ ((2 - β) * k)) =
      ((N : ℝ) * Cn)⁻¹ ^ k * (lam ^ ((2 - β) * k) * (C₁ * e₁ * R * N + C₂ * e₂ * v)) := by ring
  rw [e] at hQ
  refine (hQ.trans h).trans (le_of_eq ?_)
  rw [mul_div_assoc, div_pow_eq_div_pow_pred hNpos hk]
  field_simp

/-- **Eq. (5.68) for `𝖬^{+,Z}_{ε₀}` and `𝖬̂^{+,Z}_{ε₀}`** (Proposition 5.19, proof): for `β > 2`, `p₀ ≥ 1`, `L ∈ ℝ`, `M > 20` with `3^{p(β)} ≤ M` and
`1 ≤ k ≤ p(β)`, there is `C > 0` (depending on `χ, β, M, L, k, p₀`, not on `ε₀`) such that for every
`ε₀ ∈ (0, 1)` there are `C_{ε₀} > 0` and `λ₀ > 0` such that for every `λ ∈ (0, λ₀)` there is `N₀`
with, for `N ≥ N₀`, every frozen configuration `(V, Z)` (`I_bad^V(Z) = V`) and every
`S ⊂ [N] ∖ V` with `|S| = k`,
`|𝖬^{+,Z}_{ε₀}(S) - 𝖬^0_{ε₀}(S)| ≤ (C_{ε₀} R̄^{-2} + C ε₀^{α(β)k} |V_bad|/N) / N^{k-1}`
and the same for `𝖬̂^{+,Z}_{ε₀}(S)`. -/
theorem eq_M_plus_diff (hχ : IsMollifier χ) (hβ : 2 < β) {p₀ : ℕ} (hp₀ : 1 ≤ p₀) (L : ℝ)
    (hM : 20 < M) (hMp : (3 : ℝ) ^ pBeta p₀ β ≤ M) {k : ℕ} (hk : 1 ≤ k)
    (hkp : k ≤ pBeta p₀ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ Cε : ℝ, 0 < Cε ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
      ∀ S : Finset ℕ, S ⊆ goodLabels V → S.card = k →
        |plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S -
            zeroPartitionFunction χ N p₀ β lam M ε₀ {S}| ≤
          (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
            C * ε₀ ^ (alphaExponent β * k) * (V.card / N)) / (N : ℝ) ^ (k - 1) ∧
        |hatPartitionFunction χ N p₀ β lam M ε₀ L V Z S -
            zeroPartitionFunction χ N p₀ β lam M ε₀ {S}| ≤
          (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
            C * ε₀ ^ (alphaExponent β * k) * (V.card / N)) / (N : ℝ) ^ (k - 1) := by
  have hkp' : (k : ℕ∞) ≤ pStar β := TheoremTwo.natCast_le_pStar_of_le_pBeta hp₀ hβ hkp
  have hM0 : 0 ≤ M := by linarith
  have hM3 : 3 ≤ M := by linarith
  obtain ⟨Ca, hCa, hA⟩ := plusPartitionFunction_sub_le (χ := χ) hχ hβ hk hkp' hM0 L p₀
  obtain ⟨C₁, C₂, hC₁, hC₂, hext⟩ :=
    plusPartitionFunction_mul_external_le (χ := χ) hχ hβ hk hM3 L p₀
  set Zc := dipoleConstant χ β
  have hZ : 0 < Zc := dipoleConstant_pos hχ hβ
  refine ⟨Ca + (2 / Zc) ^ k * C₂, by positivity, fun ε₀ hε₀ hε₁ => ?_⟩
  obtain ⟨Cεa, hCεa, lama, hlama, hAε⟩ := hA ε₀ hε₀ hε₁
  obtain ⟨laml, hlaml, hlow⟩ := lem411_lower hχ hβ hε₀
  set e₁ := ε₀ ^ (tailSigma p₀ β k * k - 2)
  have he₁ : 0 ≤ e₁ := by positivity
  refine ⟨Cεa + (2 / Zc) ^ k * C₁ * e₁, by positivity, min lama (min laml ε₀),
    lt_min hlama (lt_min hlaml hε₀), fun lam hlam hlt => ?_⟩
  have hlta : lam < lama := hlt.trans_le (min_le_left _ _)
  have hltl : lam < laml := hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hlε : lam ≤ ε₀ := (hlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  obtain ⟨Na, hNa⟩ := hAε lam hlam hlta
  obtain ⟨Nl, hNl⟩ := Filter.eventually_atTop.1 (hlow p₀ lam hlam hltl)
  refine ⟨max (max Na Nl) 1, fun N hN V Z hV S _ hS => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNk : 0 < (N : ℝ) ^ (k - 1) := pow_pos hNpos _
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  set R := truncationScale p₀ β lam ^ (-2 : ℝ) with hRdef
  have hR0 : 0 ≤ R := by positivity
  set e₂ := ε₀ ^ (alphaExponent β * k)
  have he₂ : 0 ≤ e₂ := by positivity
  have hv : 0 ≤ (V.card : ℝ) / N := by positivity
  have h1 := hNa N (le_trans ((le_max_left _ _).trans (le_max_left _ _)) hN) hMp V Z hV S hS
  have hRHS : (Cεa * R + Ca * e₂ * (V.card / N)) / (N : ℝ) ^ (k - 1) ≤
      ((Cεa + (2 / Zc) ^ k * C₁ * e₁) * R + (Ca + (2 / Zc) ^ k * C₂) * e₂ * (V.card / N)) /
        (N : ℝ) ^ (k - 1) := by
    refine div_le_div_of_nonneg_right ?_ hNk.le
    have : 0 ≤ (2 / Zc) ^ k * C₁ * e₁ * R + (2 / Zc) ^ k * C₂ * e₂ * (V.card / N) := by positivity
    nlinarith
  refine ⟨h1.trans hRHS, ?_⟩
  -- the hatted version: `𝖬̂ - 𝖬^+ = 𝖬^+ (g - 1) ≥ 0`
  have hP0 : 0 ≤ plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S :=
    plusPartitionFunction_nonneg hχ hlam hε₀ hN1 S
  have hdiff : hatPartitionFunction χ N p₀ β lam M ε₀ L V Z S -
      plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S =
      plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S *
        (externalNormalization χ N p₀ β lam M ε₀ L V Z S - 1) := by
    unfold hatPartitionFunction
    ring
  have hgain : 0 ≤ plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S *
        (externalNormalization χ N p₀ β lam M ε₀ L V Z S - 1) ∧
      plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S *
        (externalNormalization χ N p₀ β lam M ε₀ L V Z S - 1) ≤
      ((2 / Zc) ^ k * C₁ * e₁ * R + (2 / Zc) ^ k * C₂ * e₂ * (V.card / N)) /
        (N : ℝ) ^ (k - 1) := by
    rcases hP0.eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul]
      exact ⟨le_rfl, by positivity⟩
    obtain ⟨hg0, hg⟩ := hext ε₀ lam hlam hlε hε₁.le hMp N hN1 V Z hV S hS hpos
    refine ⟨hg0, scaled_external_le hN1 hlam hZ
      (hNl N (le_trans ((le_max_right _ _).trans (le_max_left _ _)) hN)) hC₁ hC₂ he₁ he₂ hR0
      (Nat.cast_nonneg _) hk hg⟩
  calc |hatPartitionFunction χ N p₀ β lam M ε₀ L V Z S -
        zeroPartitionFunction χ N p₀ β lam M ε₀ {S}|
      ≤ |hatPartitionFunction χ N p₀ β lam M ε₀ L V Z S -
          plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S| +
        |plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S -
          zeroPartitionFunction χ N p₀ β lam M ε₀ {S}| := abs_sub_le _ _ _
    _ ≤ ((2 / Zc) ^ k * C₁ * e₁ * R + (2 / Zc) ^ k * C₂ * e₂ * (V.card / N)) /
          (N : ℝ) ^ (k - 1) + (Cεa * R + Ca * e₂ * (V.card / N)) / (N : ℝ) ^ (k - 1) := by
        rw [hdiff, abs_of_nonneg hgain.1]
        exact add_le_add hgain.2 h1
    _ = _ := by ring

/-- **Eq. (5.105)** (proof of Proposition 5.19): for `β > 2`,
`p₀ ≥ 1`, `L`, `M > 20` with `3^{p(β)} ≤ M` and `1 ≤ k ≤ p(β)`, there is `C > 0` (not depending on
`ε₀`) such that for every `ε₀ ∈ (0, 1)` there are `C_{ε₀} > 0` and `λ₀ > 0` such that for every
`λ ∈ (0, λ₀)` there is `N₀` with, for `N ≥ N₀`, every frozen configuration `(V, Z)` and every `S`
with `|S| = k`, `0 ≤ g^Z_{ε₀}(S) - 1 ≤ (C_{ε₀} R̄^{-2} + C ε₀^{α(β)k} |V_bad|/N) λ^{-2(k-1)}`. -/
theorem external_factor_bound (hχ : IsMollifier χ) (hβ : 2 < β) {p₀ : ℕ} (hp₀ : 1 ≤ p₀) (L : ℝ)
    (hM : 20 < M) (hMp : (3 : ℝ) ^ pBeta p₀ β ≤ M) {k : ℕ} (hk : 1 ≤ k)
    (hkp : k ≤ pBeta p₀ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ Cε : ℝ, 0 < Cε ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
      ∀ S : Finset ℕ, S.card = k →
        0 ≤ externalNormalization χ N p₀ β lam M ε₀ L V Z S - 1 ∧
        externalNormalization χ N p₀ β lam M ε₀ L V Z S - 1 ≤
          (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
            C * ε₀ ^ (alphaExponent β * k) * (V.card / N)) / lam ^ (2 * (k - 1)) := by
  have hkp' : (k : ℕ∞) ≤ pStar β := TheoremTwo.natCast_le_pStar_of_le_pBeta hp₀ hβ hkp
  have hM3 : 3 ≤ M := by linarith
  have hM9 : 9 ≤ M := by linarith
  obtain ⟨Cm, hCm, hlowM⟩ := plusPartitionFunction_two_sided (χ := χ) hχ hβ hk hkp' hM9 L
  obtain ⟨C₁, C₂, hC₁, hC₂, hext⟩ :=
    plusPartitionFunction_mul_external_le (χ := χ) hχ hβ hk hM3 L p₀
  set Zc := dipoleConstant χ β
  have hZ : 0 < Zc := dipoleConstant_pos hχ hβ
  refine ⟨Cm * ((2 / Zc) ^ k * C₂) + 1, by positivity, fun ε₀ hε₀ hε₁ => ?_⟩
  obtain ⟨lamm, hlamm, hm⟩ := hlowM ε₀ hε₀ hε₁
  obtain ⟨laml, hlaml, hlow⟩ := lem411_lower hχ hβ hε₀
  set e₁ := ε₀ ^ (tailSigma p₀ β k * k - 2)
  have he₁ : 0 ≤ e₁ := by positivity
  refine ⟨Cm * ((2 / Zc) ^ k * C₁ * e₁) + 1, by positivity, min lamm (min laml ε₀),
    lt_min hlamm (lt_min hlaml hε₀), fun lam hlam hlt => ?_⟩
  have hltm : lam < lamm := hlt.trans_le (min_le_left _ _)
  have hltl : lam < laml := hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hlε : lam ≤ ε₀ := (hlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  obtain ⟨Nm, hNm⟩ := hm p₀ lam hlam hltm
  obtain ⟨Nl, hNl⟩ := Filter.eventually_atTop.1 (hlow p₀ lam hlam hltl)
  refine ⟨max (max Nm Nl) 1, fun N hN V Z hV S hS => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNk : 0 < (N : ℝ) ^ (k - 1) := pow_pos hNpos _
  have hΛ : 0 < lam ^ (2 * (k - 1)) := pow_pos hlam _
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  set R := truncationScale p₀ β lam ^ (-2 : ℝ) with hRdef
  have hR0 : 0 ≤ R := by positivity
  set e₂ := ε₀ ^ (alphaExponent β * k)
  have he₂ : 0 ≤ e₂ := by positivity
  obtain ⟨hlo, -⟩ := hNm N (le_trans ((le_max_left _ _).trans (le_max_left _ _)) hN) hMp V Z hV S hS
  have hpos : 0 < plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S :=
    lt_of_lt_of_le (by positivity) hlo
  obtain ⟨hg0, hg⟩ := hext ε₀ lam hlam hlε hε₁.le hMp N hN1 V Z hV S hS hpos
  have hg' := scaled_external_le hN1 hlam hZ
    (hNl N (le_trans ((le_max_right _ _).trans (le_max_left _ _)) hN)) hC₁ hC₂ he₁ he₂ hR0
    (Nat.cast_nonneg _) hk hg
  have hg1 : 0 ≤ externalNormalization χ N p₀ β lam M ε₀ L V Z S - 1 :=
    (mul_nonneg_iff_of_pos_left hpos).1 hg0
  refine ⟨hg1, ?_⟩
  set Q := (2 / Zc) ^ k * C₁ * e₁ * R + (2 / Zc) ^ k * C₂ * e₂ * (V.card / N)
  have hQ0 : 0 ≤ Q := by positivity
  -- `g - 1 ≤ Q / (N^{k-1} 𝖬^+) ≤ Q C_m / λ^{2(k-1)}`
  have hdiv : externalNormalization χ N p₀ β lam M ε₀ L V Z S - 1 ≤
      Q / ((N : ℝ) ^ (k - 1) * plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S) := by
    rw [le_div_iff₀ (mul_pos hNk hpos)]
    have := (le_div_iff₀ hNk).1 hg'
    nlinarith
  have hden : lam ^ (2 * (k - 1)) / Cm ≤
      (N : ℝ) ^ (k - 1) * plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S := by
    have := mul_le_mul_of_nonneg_left hlo hNk.le
    calc lam ^ (2 * (k - 1)) / Cm = (N : ℝ) ^ (k - 1) *
          (lam ^ (2 * (k - 1)) / (Cm * (N : ℝ) ^ (k - 1))) := by field_simp
      _ ≤ _ := this
  refine hdiv.trans ?_
  calc Q / ((N : ℝ) ^ (k - 1) * plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S)
      ≤ Q / (lam ^ (2 * (k - 1)) / Cm) := div_le_div_of_nonneg_left hQ0 (by positivity) hden
    _ = Cm * Q / lam ^ (2 * (k - 1)) := by field_simp
    _ ≤ _ := by
        refine div_le_div_of_nonneg_right ?_ hΛ.le
        have : Cm * Q = Cm * ((2 / Zc) ^ k * C₁ * e₁) * R +
            Cm * ((2 / Zc) ^ k * C₂) * e₂ * (V.card / N) := by ring
        rw [this]
        have h0 : 0 ≤ R + e₂ * (V.card / N) := by positivity
        have e : (Cm * ((2 / Zc) ^ k * C₁ * e₁) + 1) * R +
            (Cm * ((2 / Zc) ^ k * C₂) + 1) * e₂ * (V.card / N) =
            Cm * ((2 / Zc) ^ k * C₁ * e₁) * R + Cm * ((2 / Zc) ^ k * C₂) * e₂ * (V.card / N) +
              (R + e₂ * (V.card / N)) := by ring
        rw [e]
        linarith

end ExpansionPlus

end UpperBound

end MultipoleBKT

end
