/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.ExpansionErrors.KDiff
public import MultipoleBKT.LowerBound.ExpansionErrors.DipoleDiff

/-!
# Proposition 4.24 (control of activity errors), from Lemmas A.7 and A.8

Proposition 4.24 (Proposition 4.24;
proof Section 4 "Control of expansion errors", Section 4.13). For `β > 2`, `2 ≤ k ≤ p*(β)`,
`ε₀ ∈ (0, 1)`, `λ` small and `N` large:

* (4.42) `|𝖬^-_{ε₀}(S) - 𝖬^0_∞(S)| ≤ C N^{1-k} R̄^{-2}` for `S ⊆ [N]`, `|S| = k`;
* (4.43) `|𝖪^dip_{β,λ,ε₀}(S) - 𝖪^dip_{β,λ}(S)| ≤ C N^{1-k} R̄^{-2}`;
* (4.44) `|𝖪^-_{ε₀}(X) - 𝖪^0_∞(X)| ≤ C R̄^{-2} / (𝖬^0_∞(X) N^{k-1})` for subpartitions `X` of
  `[N]` with `|X| > 1`, `|V_X| = k`;
* (4.45) `|𝖪^0_{ε₀}(X) - 𝖪^0_∞(X)| ≤ C R̄^{-2} / (𝖬^0_∞(X) N^{k-1})`.

`prop_4_24_of_inputs` (internal, conditional) proves the four estimates from the statements of
Lemma A.7 (`LemmaA8MinusStatement`, `LemmaA8BisStatement`) and Lemma A.8 (`LemmaI3Statement`).
These statements are proved in `MultipoleBKT.Appendix.GeneralExpansionK`
(`MultipoleBKT.ExpansionK.lemmaA8Minus_holds`, `MultipoleBKT.ExpansionK.lemmaA8Bis_holds`,
`MultipoleBKT.ExpansionK.lemmaI3_holds`). (4.42) alone is unconditional (`eq_M_diff`, for every
`1 ≤ |S| ≤ p*(β)`).

**Conventions.** `𝖬^-_{ε₀}(S) = minusPartitionFunction … {S}` (eq. (4.19)),
`𝖬^0_∞ = 𝖬_{β,λ}` (`multipolePartitionFunction`), `𝖪^-_{ε₀} = minusActivity`,
`𝖪^0_{ε₀} = zeroActivity`, `𝖪^0_∞ = zeroActivityInf` (Definition 4.15; equal to `𝖪^mult_{β,λ}` by
Corollary 4.61), `𝖪^dip_{β,λ,ε₀} = truncatedDipoleActivity` (Definition 4.20), `R̄ = R̄_{β,λ}`
(`truncationScale p₀ β λ`). The constant `C` depends on `χ, β, M, L, k, p₀, ε₀` (the paper:
`β, M, ε₀, |S|`; the mollifier and the damping constant `L` of (3.53) are fixed in the paper,
and the dependence on `p₀` for `β ≥ 4` comes from Lemma A.6, as in `GeneralExpansion`). `M` is
large (`M ≥ M₀`, `M₀ > 20`, as for Proposition 4.23).
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionErrors

open MeasureTheory Set Finset Filter
open Hierarchical

variable {χ : ℂ → ℝ} {β : ℝ}

open scoped Classical in
/-- **Proposition 4.24**, conditional on Lemmas A.7 and A.8 (internal helper;
Proposition 4.24; proof of Proposition 4.24): for `β > 2`, `L`, `p₀` and
`2 ≤ k ≤ p*(β)` there is `M₀ > 20` such that for every `M ≥ M₀` for which the statements of
Lemma A.7 (both estimates, at `M, L, p₀, k`) and of Lemma A.8 (at `p₀, k`) hold, for every
`ε₀ ∈ (0, 1)` there are `C > 0` and `λ₀ ∈ (0, 1]` such that for every `λ ∈ (0, λ₀)` there is `N₀`
with, for all `N ≥ N₀`: (4.42), (4.43), (4.44) and (4.45). -/
theorem prop_4_24_of_inputs (hχ : IsMollifier χ) (hβ : 2 < β) (L : ℝ) (p₀ : ℕ) {k : ℕ}
    (hk : 2 ≤ k) (hkp : (k : ℕ∞) ≤ pStar β) :
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      LemmaA8MinusStatement χ β M L p₀ k → LemmaA8BisStatement χ β M p₀ k →
      LemmaI3Statement χ β p₀ k →
      ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          -- (4.42)
          (∀ S : Finset ℕ, S ⊆ Finset.range N → S.card = k →
            |minusPartitionFunction χ N p₀ β lam M ε₀ L {S} -
                multipolePartitionFunction χ N β lam M S| ≤
              C / (N : ℝ) ^ (k - 1) * truncationScale p₀ β lam ^ (-2 : ℝ)) ∧
          -- (4.43)
          (∀ S : Finset ℕ, S ⊆ Finset.range N → S.card = k →
            |truncatedDipoleActivity χ N p₀ β lam ε₀ S - dipoleActivity χ N β lam S| ≤
              C / (N : ℝ) ^ (k - 1) * truncationScale p₀ β lam ^ (-2 : ℝ)) ∧
          -- (4.44)
          (∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ Finset.range N →
            1 < X.card → (X.biUnion id).card = k →
            |minusActivity χ N p₀ β lam M ε₀ L X - zeroActivityInf χ N β lam M X| ≤
              C * truncationScale p₀ β lam ^ (-2 : ℝ) /
                ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1))) ∧
          -- (4.45)
          (∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ Finset.range N →
            1 < X.card → (X.biUnion id).card = k →
            |zeroActivity χ N p₀ β lam M ε₀ X - zeroActivityInf χ N β lam M X| ≤
              C * truncationScale p₀ β lam ^ (-2 : ℝ) /
                ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1))) := by
  have hk1 : 1 ≤ k := by omega
  obtain ⟨M₁, hM₁, hK⟩ := eq_K_diff_of_lemma_A8 hχ hβ hk hkp L p₀
  obtain ⟨M₂, hM₂, hK0⟩ := eq_K_diff0_of_lemma_A8 hχ hβ hk hkp p₀
  refine ⟨max M₁ M₂, lt_max_of_lt_left hM₁, fun M hM hA8 hA8b hI3 ε₀ hε₀ hε₁ => ?_⟩
  have hMM₁ : M₁ ≤ M := (le_max_left _ _).trans hM
  have hMM₂ : M₂ ≤ M := (le_max_right _ _).trans hM
  obtain ⟨C₁, hC₁, l₁, hl₁, hl₁1, h₁⟩ :=
    eq_M_diff hχ hβ hk1 hkp (M := M) (by linarith) L p₀ ε₀ hε₀ hε₁
  obtain ⟨C₂, hC₂, l₂, hl₂, -, h₂⟩ := eq_Kdip_diff_of_lemma_I3 hχ hβ hk hkp p₀ hI3 ε₀ hε₀ hε₁
  obtain ⟨C₃, hC₃, l₃, hl₃, -, h₃⟩ := hK M hMM₁ hA8 hA8b ε₀ hε₀ hε₁
  obtain ⟨C₄, hC₄, l₄, hl₄, -, h₄⟩ := hK0 M hMM₂ hA8b ε₀ hε₀ hε₁
  set C := C₁ + C₂ + C₃ + C₄
  have hC₁C : C₁ ≤ C := by simp only [C]; linarith
  have hC₂C : C₂ ≤ C := by simp only [C]; linarith
  have hC₃C : C₃ ≤ C := by simp only [C]; linarith
  have hC₄C : C₄ ≤ C := by simp only [C]; linarith
  refine ⟨C, by positivity, min (min l₁ l₂) (min l₃ l₄),
    lt_min (lt_min hl₁ hl₂) (lt_min hl₃ hl₄),
    (min_le_left _ _).trans ((min_le_left _ _).trans hl₁1),
    fun lam hlam hlt => ?_⟩
  obtain ⟨N₁, hN₁⟩ := h₁ lam hlam (hlt.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
  obtain ⟨N₂, hN₂⟩ := h₂ lam hlam (hlt.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  obtain ⟨N₃, hN₃⟩ := h₃ lam hlam (hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨N₄, hN₄⟩ := h₄ lam hlam (hlt.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨max (max N₁ N₂) (max N₃ N₄), fun N hN => ?_⟩
  have hR : 0 ≤ truncationScale p₀ β lam ^ (-2 : ℝ) :=
    Real.rpow_nonneg (Appendix.truncationScale_pos hlam).le _
  have hT : (0 : ℝ) ≤ (N : ℝ) ^ (k - 1) := by positivity
  have hdiv : ∀ {C' : ℝ}, C' ≤ C →
      C' / (N : ℝ) ^ (k - 1) * truncationScale p₀ β lam ^ (-2 : ℝ) ≤
        C / (N : ℝ) ^ (k - 1) * truncationScale p₀ β lam ^ (-2 : ℝ) := fun h =>
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h hT) hR
  have hdiv' : ∀ {C' : ℝ} (X : Finset (Finset ℕ)), C' ≤ C →
      C' * truncationScale p₀ β lam ^ (-2 : ℝ) /
          ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1)) ≤
        C * truncationScale p₀ β lam ^ (-2 : ℝ) /
          ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1)) :=
    fun X h => div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h hR)
      (mul_nonneg (prod_nonneg fun S _ => multipolePartitionFunction_nonneg χ N β lam M S) hT)
  refine ⟨fun S _ hS => ?_, fun S hS hSk => ?_, fun X hX hXN hX1 hXk => ?_,
    fun X hX hXN hX1 hXk => ?_⟩
  · exact (hN₁ N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN) S hS).trans
      (hdiv hC₁C)
  · exact (hN₂ N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN) S hS hSk).trans
      (hdiv hC₂C)
  · exact (hN₃ N (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN) X hX hXN hX1
      hXk).trans (hdiv' X hC₃C)
  · exact (hN₄ N (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN) X hX hXN hX1
      hXk).trans (hdiv' X hC₄C)

end ExpansionErrors

end MultipoleBKT

end
