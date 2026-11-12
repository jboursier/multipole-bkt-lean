/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.ExpansionPlus.Hat

/-!
# Proposition 5.19 (expansion errors with frozen bad points)

The paper: Proposition 5.19; proof. Let `β > 2`, `ε₀ ∈ (0, 1)`, `V_bad ⊂ [N]`, `Z` a frozen configuration of bad points,
`S ⊂ V_good` with `1 ≤ |S| ≤ p(β)` and `X` a subpartition of `V_good` with `|V_X| ≤ p(β)`. For `λ`
small there are `C > 0` (depending on `β, M, |S|`, resp. `|V_X|`) and `C_{ε₀} > 0` (also depending on
`ε₀`) such that, with `θ_s = C_{ε₀} R̄^{-2} + C ε₀^{α(β)s} |V_bad|/N`,

* (5.68) `|𝖬^{+,Z}_{ε₀}(S) - 𝖬^0_{ε₀}(S)| ≤ θ_{|S|} / N^{|S|-1}`;
* (5.69) `|𝖪^{+,Z}_{ε₀}(X) - 𝖪^0_{ε₀}(X)| ≤ θ_{|V_X|} / (N^{|V_X|-1} 𝖬^0_{ε₀}(X))`;

and the same for `𝖬̂^{+,Z}_{ε₀}`, `𝖪̂^{+,Z}_{ε₀}`.

* `eq_M_plus_diff` (in `MultipoleBKT.UpperBound.ExpansionPlus.MultipoleHat`): (5.68) for
  `𝖬^{+,Z}_{ε₀}` and `𝖬̂^{+,Z}_{ε₀}`, **unconditional**;
* `eq_K_hat_diff_of_inputs` (internal): (5.69) for `𝖪̂^{+,Z}_{ε₀}` from the inputs;
* `prop_5_19_of_inputs` (internal): **Proposition 5.19** for one size `k ≤ p(β)` (both (5.68)
  with `|S| = k` and (5.69) with `|V_X| = k`, for the four objects), from the inputs of
  `MultipoleBKT.UpperBound.ExpansionPlus.Inputs` (Lemma A.7 for `(v^Z, τ^Z)`, Lemma A.7
  (A.50), and the claim (5.106)), which are needed only for
  `k ≥ 2`.

**Conventions.** `𝖬^{+,Z}_{ε₀} = plusPartitionFunction`, `𝖬̂^{+,Z}_{ε₀} = hatPartitionFunction`,
`𝖪^{+,Z}_{ε₀} = plusActivity`, `𝖪̂^{+,Z}_{ε₀} = hatActivity` (Definitions 5.13–5.15),
`𝖬^0_{ε₀}(S) = zeroPartitionFunction … {S}`, `𝖪^0_{ε₀} = zeroActivity`,
`R̄ = truncationScale p₀ β λ`, `α(β) = alphaExponent β`; the bad points are frozen
(`I_bad^V(Z) = V`, Section 5.3); the good labels are `goodLabels V = [N] ∖ V`.
The constants depend on `χ, β, M, L, k, p₀` (the paper: `β, M, |S|`; the mollifier and `L` are
fixed in the paper, and the dependence on `p₀` for `β ≥ 4` comes from Lemma A.6); `C` does not
depend on `ε₀`. `M ≥ M₀` with `M₀ > 20` (from (4.40) and Proposition 4.24) and `3^{p(β)} ≤ M` (the paper's `M > max(20, 3^{p(β)})`). The paper's
"for `λ` small enough" is `λ < λ₀(ε₀)`, and `N` is large (`N ≥ N₀(ε₀, λ)`).

**The comparison (5.68).** First compare with `𝖬^0_∞`, then use the triangle inequality
to compare at the same cutoff, as in the paper
(`MultipoleBKT.UpperBound.ExpansionPlus.MultipoleDiff`).
-/

@[expose] public section

namespace MultipoleBKT

namespace UpperBound

namespace ExpansionPlus

open MeasureTheory Set Finset Filter
open Hierarchical BoundedUpper ExpansionErrors

variable {χ : ℂ → ℝ} {β : ℝ}

/-- **Eq. (5.69) for `𝖪̂^{+,Z}_{ε₀}`, from the inputs** (internal helper; Proposition 5.19, proof). Same quantifiers as `eq_K_plus_diff_of_inputs`, with `p₀ ≥ 1` and
`2 ≤ k ≤ p(β)`. -/
theorem eq_K_hat_diff_of_inputs (hχ : IsMollifier χ) (hβ : 2 < β) {p₀ : ℕ} (hp₀ : 1 ≤ p₀)
    (L : ℝ) {k : ℕ} (hk : 2 ≤ k) (hkp : k ≤ pBeta p₀ β) :
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M → (3 : ℝ) ^ pBeta p₀ β ≤ M →
      LemmaA8PlusStatement χ β M L p₀ k → LemmaA8BisStatement χ β M p₀ k →
      NonEmptyMarksStatement χ β M L p₀ k →
      ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ Cε : ℝ, 0 < Cε ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
        ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ goodLabels V →
          (X.biUnion id).card = k →
          |plusActivity χ N p₀ β lam M ε₀ L V Z X - zeroActivity χ N p₀ β lam M ε₀ X| ≤
              (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
                  C * ε₀ ^ (alphaExponent β * k) * (V.card / N)) /
                ((N : ℝ) ^ (k - 1) * zeroPartitionFunction χ N p₀ β lam M ε₀ X) ∧
            |hatActivity χ N p₀ β lam M ε₀ L V Z X - zeroActivity χ N p₀ β lam M ε₀ X| ≤
              (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
                  C * ε₀ ^ (alphaExponent β * k) * (V.card / N)) /
                ((N : ℝ) ^ (k - 1) * zeroPartitionFunction χ N p₀ β lam M ε₀ X) := by
  have hkp' : (k : ℕ∞) ≤ pStar β := TheoremTwo.natCast_le_pStar_of_le_pBeta hp₀ hβ hkp
  obtain ⟨M₁, hM₁, hK⟩ := eq_K_plus_diff_of_inputs (χ := χ) hχ hβ L p₀ hk hkp'
  obtain ⟨M₂, hM₂, hH⟩ := zeroActivity_mul_external_le (χ := χ) hχ hβ hp₀ L hk hkp
  refine ⟨max M₁ M₂, lt_max_of_lt_left hM₁, fun M hM hMp hA8 hA8b hNE => ?_⟩
  obtain ⟨C₁, hC₁, h₁⟩ := hK M ((le_max_left _ _).trans hM) hMp hA8 hA8b hNE
  obtain ⟨C₂, hC₂, h₂⟩ := hH M ((le_max_right _ _).trans hM) hMp hA8b
  refine ⟨C₁ + C₂, by positivity, fun ε₀ hε₀ hε₁ => ?_⟩
  obtain ⟨D₁, hD₁, l₁, hl₁, h₁'⟩ := h₁ ε₀ hε₀ hε₁
  obtain ⟨D₂, hD₂, l₂, hl₂, h₂'⟩ := h₂ ε₀ hε₀ hε₁
  refine ⟨D₁ + D₂, by positivity, min l₁ l₂, lt_min hl₁ hl₂, fun lam hlam hlt => ?_⟩
  obtain ⟨N₁, hN₁⟩ := h₁' lam hlam (hlt.trans_le (min_le_left _ _))
  obtain ⟨N₂, hN₂⟩ := h₂' lam hlam (hlt.trans_le (min_le_right _ _))
  refine ⟨max (max N₁ N₂) 1, fun N hN V Z hV X hX hXV hXk => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have e1 := hN₁ N (le_trans ((le_max_left _ _).trans (le_max_left _ _)) hN) V Z hV X hX hXV hXk
  obtain ⟨hG1, e2⟩ := hN₂ N (le_trans ((le_max_right _ _).trans (le_max_left _ _)) hN) V Z hV X
    hX hXV hXk
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  set R := truncationScale p₀ β lam ^ (-2 : ℝ) with hRdef
  have hR0 : 0 ≤ R := by positivity
  set e := ε₀ ^ (alphaExponent β * k)
  have he : 0 ≤ e := by positivity
  set v : ℝ := V.card / N
  have hv : 0 ≤ v := by positivity
  have hden : 0 ≤ (N : ℝ) ^ (k - 1) * zeroPartitionFunction χ N p₀ β lam M ε₀ X := by
    refine mul_nonneg (by positivity) ?_
    unfold zeroPartitionFunction
    exact prod_nonneg fun S _ =>
      (modelHyp_zero (p₀ := p₀) hχ hlam β hε₀ hN1).modelPartitionFunction_nonneg M lam S
  have hmono : ∀ {a b c d : ℝ}, a ≤ c → b ≤ d →
      (a * R + b * e * v) / ((N : ℝ) ^ (k - 1) * zeroPartitionFunction χ N p₀ β lam M ε₀ X) ≤
        (c * R + d * e * v) / ((N : ℝ) ^ (k - 1) * zeroPartitionFunction χ N p₀ β lam M ε₀ X) := by
    intro a b c d hac hbd
    refine div_le_div_of_nonneg_right ?_ hden
    have h1 := mul_le_mul_of_nonneg_right hac hR0
    have h2 := mul_le_mul_of_nonneg_right hbd (mul_nonneg he hv)
    nlinarith
  refine ⟨e1.trans (hmono (by linarith) (by linarith)), ?_⟩
  have hhat : hatActivity χ N p₀ β lam M ε₀ L V Z X =
      plusActivity χ N p₀ β lam M ε₀ L V Z X /
        ∏ S ∈ X, externalNormalization χ N p₀ β lam M ε₀ L V Z S := rfl
  rw [hhat]
  refine (hat_arith hG1).trans ?_
  calc |plusActivity χ N p₀ β lam M ε₀ L V Z X - zeroActivity χ N p₀ β lam M ε₀ X| +
        |zeroActivity χ N p₀ β lam M ε₀ X| *
          (∏ S ∈ X, externalNormalization χ N p₀ β lam M ε₀ L V Z S - 1)
      ≤ (D₁ * R + C₁ * e * v) / ((N : ℝ) ^ (k - 1) * zeroPartitionFunction χ N p₀ β lam M ε₀ X) +
          (D₂ * R + C₂ * e * v) /
            ((N : ℝ) ^ (k - 1) * zeroPartitionFunction χ N p₀ β lam M ε₀ X) := add_le_add e1 e2
    _ = ((D₁ + D₂) * R + (C₁ + C₂) * e * v) /
          ((N : ℝ) ^ (k - 1) * zeroPartitionFunction χ N p₀ β lam M ε₀ X) := by ring

/-- For a subpartition with `|V_X| ≤ 1`, all the activities vanish (`|X| ≤ 1`). -/
theorem activities_eq_zero_of_card_le_one {N p₀ : ℕ} {lam M ε₀ L : ℝ} {V : Finset (Fin N)}
    {Z : Fin N → ℂ × ℂ} {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    (hk : (X.biUnion id).card ≤ 1) :
    plusActivity χ N p₀ β lam M ε₀ L V Z X = 0 ∧ hatActivity χ N p₀ β lam M ε₀ L V Z X = 0 ∧
      zeroActivity χ N p₀ β lam M ε₀ X = 0 := by
  have h1 : X.card ≤ 1 := (card_le_card_biUnion hX).trans hk
  exact ⟨plusActivity_eq_zero_of_card_le_one χ p₀ β lam M ε₀ L V Z h1,
    hatActivity_eq_zero_of_card_le_one χ p₀ β lam M ε₀ L V Z h1,
    modelActivity_eq_zero_of_card_le_one _ _ _ _ _ _ h1⟩

open scoped Classical in
/-- **Proposition 5.19, from the inputs** (internal helper; Proposition 5.19, proof), for one size `k ≤ p(β)`: for `β > 2`, `p₀ ≥ 1`, `L` there is
`M₀ > 20` such that for every `M ≥ M₀` with `3^{p(β)} ≤ M` for which, when `k ≥ 2`, the inputs
`LemmaA8PlusStatement`, `ExpansionErrors.LemmaA8BisStatement` and `NonEmptyMarksStatement` hold at
`M, L, p₀, k`, there is `C > 0` (not depending on `ε₀`) such that for every `ε₀ ∈ (0, 1)` there are
`C_{ε₀} > 0` and `λ₀ > 0` such that for every `λ ∈ (0, λ₀)` there is `N₀` with, for `N ≥ N₀` and
every frozen configuration `(V, Z)` (`I_bad^V(Z) = V`), with `θ = C_{ε₀} R̄^{-2} + C ε₀^{α(β)k}
|V_bad|/N`:

* (5.68), for `k ≥ 1` and `S ⊂ [N] ∖ V` with `|S| = k`:
  `|𝖬^{+,Z}_{ε₀}(S) - 𝖬^0_{ε₀}(S)| ≤ θ / N^{k-1}` and `|𝖬̂^{+,Z}_{ε₀}(S) - 𝖬^0_{ε₀}(S)| ≤ θ / N^{k-1}`;
* (5.69), for every subpartition `X` of `[N] ∖ V` with `|V_X| = k`:
  `|𝖪^{+,Z}_{ε₀}(X) - 𝖪^0_{ε₀}(X)| ≤ θ / (N^{k-1} 𝖬^0_{ε₀}(X))` and the same for `𝖪̂^{+,Z}_{ε₀}`.

The inputs are used only for (5.69) with `k ≥ 2`; (5.68) is unconditional
(`eq_M_plus_diff`). -/
theorem prop_5_19_of_inputs (hχ : IsMollifier χ) (hβ : 2 < β) {p₀ : ℕ} (hp₀ : 1 ≤ p₀) (L : ℝ)
    {k : ℕ} (hkp : k ≤ pBeta p₀ β) :
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M → (3 : ℝ) ^ pBeta p₀ β ≤ M →
      (2 ≤ k → LemmaA8PlusStatement χ β M L p₀ k ∧ LemmaA8BisStatement χ β M p₀ k ∧
        NonEmptyMarksStatement χ β M L p₀ k) →
      ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ Cε : ℝ, 0 < Cε ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
          (1 ≤ k → ∀ S : Finset ℕ, S ⊆ goodLabels V → S.card = k →
            |plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S -
                zeroPartitionFunction χ N p₀ β lam M ε₀ {S}| ≤
              (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
                C * ε₀ ^ (alphaExponent β * k) * (V.card / N)) / (N : ℝ) ^ (k - 1) ∧
            |hatPartitionFunction χ N p₀ β lam M ε₀ L V Z S -
                zeroPartitionFunction χ N p₀ β lam M ε₀ {S}| ≤
              (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
                C * ε₀ ^ (alphaExponent β * k) * (V.card / N)) / (N : ℝ) ^ (k - 1)) ∧
          (∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ goodLabels V →
            (X.biUnion id).card = k →
            |plusActivity χ N p₀ β lam M ε₀ L V Z X - zeroActivity χ N p₀ β lam M ε₀ X| ≤
                (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
                    C * ε₀ ^ (alphaExponent β * k) * (V.card / N)) /
                  ((N : ℝ) ^ (k - 1) * zeroPartitionFunction χ N p₀ β lam M ε₀ X) ∧
              |hatActivity χ N p₀ β lam M ε₀ L V Z X - zeroActivity χ N p₀ β lam M ε₀ X| ≤
                (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
                    C * ε₀ ^ (alphaExponent β * k) * (V.card / N)) /
                  ((N : ℝ) ^ (k - 1) * zeroPartitionFunction χ N p₀ β lam M ε₀ X)) := by
  -- the (5.69) part, for `k ≥ 2` from the inputs, for `k ≤ 1` trivially
  have hK : ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M → (3 : ℝ) ^ pBeta p₀ β ≤ M →
      (2 ≤ k → LemmaA8PlusStatement χ β M L p₀ k ∧ LemmaA8BisStatement χ β M p₀ k ∧
        NonEmptyMarksStatement χ β M L p₀ k) →
      ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ Cε : ℝ, 0 < Cε ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
        ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ goodLabels V →
          (X.biUnion id).card = k →
          |plusActivity χ N p₀ β lam M ε₀ L V Z X - zeroActivity χ N p₀ β lam M ε₀ X| ≤
              (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
                  C * ε₀ ^ (alphaExponent β * k) * (V.card / N)) /
                ((N : ℝ) ^ (k - 1) * zeroPartitionFunction χ N p₀ β lam M ε₀ X) ∧
            |hatActivity χ N p₀ β lam M ε₀ L V Z X - zeroActivity χ N p₀ β lam M ε₀ X| ≤
              (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
                  C * ε₀ ^ (alphaExponent β * k) * (V.card / N)) /
                ((N : ℝ) ^ (k - 1) * zeroPartitionFunction χ N p₀ β lam M ε₀ X) := by
    by_cases hk2 : 2 ≤ k
    · obtain ⟨M₀, hM₀, h⟩ := eq_K_hat_diff_of_inputs (χ := χ) hχ hβ hp₀ L hk2 hkp
      exact ⟨M₀, hM₀, fun M hM hMp hin => h M hM hMp (hin hk2).1 (hin hk2).2.1 (hin hk2).2.2⟩
    · refine ⟨21, by norm_num, fun M hM hMp _ => ⟨1, one_pos, fun ε₀ hε₀ _ => ⟨1, one_pos, 1,
        one_pos, fun lam hlam _ => ⟨1, fun N hN V Z hV X hX hXV hXk => ?_⟩⟩⟩⟩
      obtain ⟨h1, h2, h3⟩ := activities_eq_zero_of_card_le_one (β := β) (χ := χ) (p₀ := p₀)
        (lam := lam) (M := M) (ε₀ := ε₀) (L := L) (V := V) (Z := Z) hX (by omega)
      rw [h1, h2, h3, sub_zero, abs_zero]
      have hN1 : (0 : ℝ) < N := by exact_mod_cast hN
      have hden : 0 ≤ (N : ℝ) ^ (k - 1) * zeroPartitionFunction χ N p₀ β lam M ε₀ X := by
        refine mul_nonneg (by positivity) ?_
        unfold zeroPartitionFunction
        exact prod_nonneg fun S _ =>
          (modelHyp_zero (p₀ := p₀) hχ hlam β hε₀ hN).modelPartitionFunction_nonneg M lam S
      have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
      have hnum : 0 ≤ 1 * truncationScale p₀ β lam ^ (-2 : ℝ) +
          1 * ε₀ ^ (alphaExponent β * k) * ((V.card : ℝ) / N) := by positivity
      exact ⟨div_nonneg hnum hden, div_nonneg hnum hden⟩
  -- the (5.68) part (unconditional)
  have hMd : ∀ M : ℝ, 20 < M → (3 : ℝ) ^ pBeta p₀ β ≤ M →
      ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ Cε : ℝ, 0 < Cε ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
          1 ≤ k → ∀ S : Finset ℕ, S ⊆ goodLabels V → S.card = k →
            |plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S -
                zeroPartitionFunction χ N p₀ β lam M ε₀ {S}| ≤
              (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
                C * ε₀ ^ (alphaExponent β * k) * (V.card / N)) / (N : ℝ) ^ (k - 1) ∧
            |hatPartitionFunction χ N p₀ β lam M ε₀ L V Z S -
                zeroPartitionFunction χ N p₀ β lam M ε₀ {S}| ≤
              (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
                C * ε₀ ^ (alphaExponent β * k) * (V.card / N)) / (N : ℝ) ^ (k - 1) := by
    intro M hM hMp
    by_cases hk1 : 1 ≤ k
    · obtain ⟨C, hC, h⟩ := eq_M_plus_diff (χ := χ) hχ hβ hp₀ L hM hMp hk1 hkp
      refine ⟨C, hC, fun ε₀ hε₀ hε₁ => ?_⟩
      obtain ⟨Cε, hCε, lam₀, hlam₀, h'⟩ := h ε₀ hε₀ hε₁
      refine ⟨Cε, hCε, lam₀, hlam₀, fun lam hlam hlt => ?_⟩
      obtain ⟨N₀, hN₀⟩ := h' lam hlam hlt
      exact ⟨N₀, fun N hN V Z hV _ S hS hSk => hN₀ N hN V Z hV S hS hSk⟩
    · exact ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, 1, one_pos, fun _ _ _ =>
        ⟨0, fun _ _ _ _ _ h => absurd h hk1⟩⟩⟩
  obtain ⟨M₀, hM₀, hK'⟩ := hK
  refine ⟨M₀, hM₀, fun M hM hMp hin => ?_⟩
  have hM20 : 20 < M := lt_of_lt_of_le hM₀ hM
  obtain ⟨C₁, hC₁, h₁⟩ := hK' M hM hMp hin
  obtain ⟨C₂, hC₂, h₂⟩ := hMd M hM20 hMp
  refine ⟨C₁ + C₂, by positivity, fun ε₀ hε₀ hε₁ => ?_⟩
  obtain ⟨D₁, hD₁, l₁, hl₁, h₁'⟩ := h₁ ε₀ hε₀ hε₁
  obtain ⟨D₂, hD₂, l₂, hl₂, h₂'⟩ := h₂ ε₀ hε₀ hε₁
  refine ⟨D₁ + D₂, by positivity, min l₁ l₂, lt_min hl₁ hl₂, fun lam hlam hlt => ?_⟩
  obtain ⟨N₁, hN₁⟩ := h₁' lam hlam (hlt.trans_le (min_le_left _ _))
  obtain ⟨N₂, hN₂⟩ := h₂' lam hlam (hlt.trans_le (min_le_right _ _))
  refine ⟨max (max N₁ N₂) 1, fun N hN V Z hV => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  set R := truncationScale p₀ β lam ^ (-2 : ℝ) with hRdef
  have hR0 : 0 ≤ R := by positivity
  set e := ε₀ ^ (alphaExponent β * k)
  have he : 0 ≤ e := by positivity
  set v : ℝ := V.card / N
  have hv : 0 ≤ v := by positivity
  have hmono : ∀ {a b c d D : ℝ}, 0 ≤ D → a ≤ c → b ≤ d →
      (a * R + b * e * v) / D ≤ (c * R + d * e * v) / D := by
    intro a b c d D hD hac hbd
    refine div_le_div_of_nonneg_right ?_ hD
    have h1 := mul_le_mul_of_nonneg_right hac hR0
    have h2 := mul_le_mul_of_nonneg_right hbd (mul_nonneg he hv)
    nlinarith
  refine ⟨fun hk1 S hS hSk => ?_, fun X hX hXV hXk => ?_⟩
  · obtain ⟨e1, e2⟩ := hN₂ N (le_trans ((le_max_right _ _).trans (le_max_left _ _)) hN) V Z hV hk1
      S hS hSk
    have hT : (0 : ℝ) ≤ (N : ℝ) ^ (k - 1) := by positivity
    exact ⟨e1.trans (hmono hT (by linarith) (by linarith)),
      e2.trans (hmono hT (by linarith) (by linarith))⟩
  · obtain ⟨e1, e2⟩ := hN₁ N (le_trans ((le_max_left _ _).trans (le_max_left _ _)) hN) V Z hV X
      hX hXV hXk
    have hD : 0 ≤ (N : ℝ) ^ (k - 1) * zeroPartitionFunction χ N p₀ β lam M ε₀ X := by
      refine mul_nonneg (by positivity) ?_
      unfold zeroPartitionFunction
      exact prod_nonneg fun S _ =>
        (modelHyp_zero (p₀ := p₀) hχ hlam β hε₀ hN1).modelPartitionFunction_nonneg M lam S
    exact ⟨e1.trans (hmono hD (by linarith) (by linarith)),
      e2.trans (hmono hD (by linarith) (by linarith))⟩

end ExpansionPlus

end UpperBound

end MultipoleBKT

end
