/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.ExpansionErrors.Normalization
public import MultipoleBKT.Appendix.GeneralExpansion.MinusModel

/-!
# Proposition 4.24, eq. (4.42)

Proposition 4.24,
eq. (4.42) (Proposition 4.24); proof of Proposition 4.24: for `1 ≤ |S| = k ≤ p*(β)`,

`|𝖬^-_{ε₀}(S) - 𝖬^0_∞(S)| ≤ C N^{1-k} R̄^{-2}`.

**Proof** (eq. (4.75)). With `a = (N C_{β,λ,ε₀})⁻¹`, `b = (N C_{β,λ})⁻¹`, `𝖬^-_{ε₀}(S) = a^k I^-`
and `𝖬^0_∞(S) = b^k I^0` (the normalization identities `minusPartitionFunction_singleton_eq`,
`multipolePartitionFunction_eq_multipoleIntegral`), so
`|𝖬^- - 𝖬^0| ≤ a^k |I^- - I^0| + |(a/b)^k - 1| 𝖬^0_∞(S)` (`abs_mul_pow_sub_mul_pow_le`).
Lemma A.6 (`GeneralExpansion.multipoleIntegralMinus_sub_le`) and (4.12) bound the
first term by `C N^{1-k} R̄^{-2}` (eq. (4.76)); (4.13) gives
`|(a/b)^k - 1| ≤ C R̄^{-2}` and (4.39) (`multipoleIntegral_le`) `𝖬^0_∞(S) ≤ C λ^{2(k-1)} N^{1-k}`
(eq. (4.77)). The paper states (4.42) for `1 < |S|`; the proof covers `|S| = 1` as well (the
singleton estimate used in the proof of Proposition 4.62, (4.142)).

* `abs_normalized_sub_le`: the arithmetic of (4.76)–(4.77), shared with (4.43);
* `eq_M_diff`: (4.42).
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionErrors

open MeasureTheory Set Finset Metric Filter
open TwoComponentCoulomb (box)
open Hierarchical

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ L : ℝ}

/-- **The arithmetic of (4.76)–(4.77).** Let `A = N C_ε ≥ N (Z/2) ℓ` and `B = N C > 0` with
`|C/C_ε - 1| ≤ δ`, `C/C_ε ≤ 2`, `|J₁ - J₂| ≤ D N ℓ^k Λ` and `|B^{-k} J₂| ≤ Q`. Then
`|A^{-k} J₁ - B^{-k} J₂| ≤ D (2/Z)^k Λ / N^{k-1} + k 2^{k-1} δ Q`. -/
theorem abs_normalized_sub_le {k : ℕ} (hk : 1 ≤ k) {N Z ℓ Ce C J₁ J₂ D Λ δ Q : ℝ}
    (hN : 0 < N) (hZ : 0 < Z) (hℓ : 0 < ℓ) (hCe : Z / 2 * ℓ ≤ Ce) (hC : 0 < C)
    (hratio : C / Ce ≤ 2) (hδ : |C / Ce - 1| ≤ δ)
    (hJ : |J₁ - J₂| ≤ D * N * ℓ ^ k * Λ) (hQ : |(N * C)⁻¹ ^ k * J₂| ≤ Q) :
    |(N * Ce)⁻¹ ^ k * J₁ - (N * C)⁻¹ ^ k * J₂| ≤
      D * (2 / Z) ^ k * Λ / N ^ (k - 1) + k * 2 ^ (k - 1) * δ * Q := by
  have hCe0 : 0 < Ce := lt_of_lt_of_le (by positivity) hCe
  have ha : 0 < (N * Ce)⁻¹ := inv_pos.2 (mul_pos hN hCe0)
  have hb : 0 < (N * C)⁻¹ := inv_pos.2 (mul_pos hN hC)
  have hab : (N * Ce)⁻¹ / (N * C)⁻¹ = C / Ce := by
    field_simp
  have h1 := abs_mul_pow_sub_mul_pow_le ha hb k J₁ J₂
  rw [hab] at h1
  refine h1.trans (add_le_add ?_ ?_)
  · have hA : N * (Z / 2) * ℓ ≤ N * Ce := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hCe hN.le
    exact MultipoleIntegral.gate_upper_algebra hk hN hℓ hZ hA hJ (abs_nonneg _)
  · have hx0 : 0 ≤ C / Ce := (div_pos hC hCe0).le
    have h2 := abs_pow_sub_one_le hx0 hratio k
    have hQ0 : 0 ≤ Q := (abs_nonneg _).trans hQ
    calc |(C / Ce) ^ k - 1| * |(N * C)⁻¹ ^ k * J₂|
        ≤ (k * 2 ^ (k - 1) * |C / Ce - 1|) * Q :=
          mul_le_mul h2 hQ (abs_nonneg _) (by positivity)
      _ ≤ (k * 2 ^ (k - 1) * δ) * Q := by gcongr
      _ = k * 2 ^ (k - 1) * δ * Q := by ring

/-- `λ^{(2-β)k} = (λ^{2-β})^k`. -/
theorem rpow_mul_natCast_eq (hlam : 0 < lam) (k : ℕ) :
    lam ^ ((2 - β) * k) = (lam ^ (2 - β)) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hlam.le]

/-- **Proposition 4.24, eq. (4.42)** (Proposition 4.24; proof of Proposition 4.24): for `β > 2`, `1 ≤ k ≤ p*(β)`, `M ≥ 0`, `L ∈ ℝ`, `p₀` and `ε₀ ∈ (0, 1)` there are
`C > 0` and `λ₀ ∈ (0, 1]` such that for `λ ∈ (0, λ₀)` there is `N₀` with
`|𝖬^-_{ε₀}(S) - 𝖬^0_∞(S)| ≤ C N^{1-k} R̄^{-2}` for all `N ≥ N₀` and `|S| = k`. Here
`𝖬^0_∞ = 𝖬_{β,λ}` (`modelPartitionFunction_dipoleMeasure`). `C` depends on `χ, β, M, L, k, p₀`
and `ε₀`. -/
theorem eq_M_diff (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 1 ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) (hM : 0 ≤ M) (L : ℝ) (p₀ : ℕ) :
    ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ S : Finset ℕ, S.card = k →
          |minusPartitionFunction χ N p₀ β lam M ε₀ L {S} -
              multipolePartitionFunction χ N β lam M S| ≤
            C / (N : ℝ) ^ (k - 1) * truncationScale p₀ β lam ^ (-2 : ℝ) := by
  intro ε₀ hε₀ hε₁
  obtain ⟨CA, hCA, hA7⟩ := GeneralExpansion.multipoleIntegralMinus_sub_le hχ hβ hk hkp hM L p₀
    ε₀ hε₀
  obtain ⟨Cu, hCu, hup⟩ := multipoleIntegral_le hχ hβ hk hkp hM
  obtain ⟨Cn, hCn, lam₀, hlam₀, hlam₀1, hnorm⟩ := normalization_bounds hχ hβ p₀ ε₀ hε₀ hε₁
  set Z := dipoleConstant χ β
  have hZ : 0 < Z := dipoleConstant_pos hχ hβ
  refine ⟨CA * (2 / Z) ^ k + k * 2 ^ (k - 1) * Cn * (Cu * (2 / Z) ^ k), by positivity, lam₀,
    hlam₀, hlam₀1, fun lam hlam hlt => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hnorm lam hlam hlt
  refine ⟨N₀, fun N hN S hS => ?_⟩
  obtain ⟨hN1, h2, hCe, -, hC, hCZ, hδ⟩ := hN₀ N hN
  have hlam1 : lam ≤ 1 := (hlt.trans_le hlam₀1).le
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hℓ : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  set R := truncationScale p₀ β lam
  have hR : 0 < R := Appendix.truncationScale_pos hlam
  set Ce := cutoffDipoleNormalization χ N p₀ β lam ε₀
  set C := dipoleNormalization χ N β lam
  have hC0 : 0 < C := lt_of_lt_of_le (by positivity) hC
  have hCe0 : 0 < Ce := lt_of_lt_of_le (by positivity) hCe
  have hratio : C / Ce ≤ 2 := by
    rw [div_le_iff₀ hCe0]
    nlinarith
  have hCe' : Z / 2 * lam ^ (2 - β) ≤ Ce := by linarith
  -- the normalization identities
  rw [BoundedLowerEps.minusPartitionFunction_singleton_eq hχ hlam hε₀ hN1 S,
    multipolePartitionFunction_eq_multipoleIntegral hχ hlam β M hN1 S, hS]
  -- Lemma A.6
  have hJ : |multipoleIntegralMinus χ N β lam M L ε₀ R S - multipoleIntegral χ N β lam M S| ≤
      CA * N * (lam ^ (2 - β)) ^ k * R ^ (-2 : ℝ) := by
    have := hA7 lam hlam hlam1 (by linarith) N S hS
    rw [rpow_mul_natCast_eq hlam k] at this
    linarith
  -- (4.39)
  have hQ : |((N : ℝ) * C)⁻¹ ^ k * multipoleIntegral χ N β lam M S| ≤
      Cu * (2 / Z) ^ k / (N : ℝ) ^ (k - 1) := by
    have hI0 : 0 ≤ multipoleIntegral χ N β lam M S := by
      rw [multipoleIntegral_eq_toReal_lintegral hχ hlam N β M S]
      exact ENNReal.toReal_nonneg
    have hI := hup lam hlam N S hS
    rw [rpow_mul_natCast_eq hlam k] at hI
    have hA : (N : ℝ) * (Z / 2) * lam ^ (2 - β) ≤ N * C := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hNpos.le
      linarith
    have h := MultipoleIntegral.gate_upper_algebra hk hNpos hℓ hZ hA hI hI0
    rw [abs_of_nonneg (mul_nonneg (pow_nonneg (inv_nonneg.2 (by positivity)) _) hI0)]
    refine h.trans ?_
    have hΛ : lam ^ (2 * (k - 1)) ≤ 1 := pow_le_one₀ hlam.le hlam1
    have hNk : 0 < (N : ℝ) ^ (k - 1) := by positivity
    rw [div_le_div_iff_of_pos_right hNk]
    calc Cu * (2 / Z) ^ k * lam ^ (2 * (k - 1)) ≤ Cu * (2 / Z) ^ k * 1 := by gcongr
      _ = Cu * (2 / Z) ^ k := mul_one _
  have h := abs_normalized_sub_le hk hNpos hZ hℓ hCe' hC0 hratio hδ hJ hQ
  refine h.trans (le_of_eq ?_)
  ring

end ExpansionErrors

end MultipoleBKT

end
