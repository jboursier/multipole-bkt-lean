/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.ExpansionErrors.Normalization
public import MultipoleBKT.Appendix.MultipoleIntegral.RouteChain.Cutoff

/-!
# Transfer of the truncated zero normalizer

The proof of Proposition 4.23. Restrict the untruncated integral to the radial cutoff,
then compare its normalization with the truncated zero model.
-/

@[expose] public section

namespace MultipoleBKT.LowerBound.RouteBounded

open MeasureTheory Finset Hierarchical MultipoleIntegral
open scoped Classical

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ : ℝ}

/-- Restriction of the numerator, retaining the exact ratio of the two
normalizations. See the proof of Proposition 4.23. -/
theorem zeroPartitionFunction_transfer (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hε₀ : 0 < ε₀) (hN : 1 ≤ N) (S : Finset ℕ) :
    (cutoffDipoleNormalization χ N p₀ β lam ε₀ / dipoleNormalization χ N β lam) ^ S.card *
        zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ≤
      multipolePartitionFunction χ N β lam M S := by
  rw [ExpansionErrors.zeroPartitionFunction_singleton_eq hχ hlam hε₀ hN S,
    multipolePartitionFunction_eq_multipoleIntegral hχ hlam β M hN S]
  have hcut := cutoffDipoleNormalization_pos (p₀ := p₀) hχ hlam β hε₀ hN
  have hfull := dipoleNormalization_pos hχ hlam β hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have heq : (cutoffDipoleNormalization χ N p₀ β lam ε₀ / dipoleNormalization χ N β lam) ^ S.card *
      (((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^ S.card *
        multipoleIntegralCut χ N β lam M (ε₀ * truncationScale p₀ β lam) S) =
      ((N : ℝ) * dipoleNormalization χ N β lam)⁻¹ ^ S.card *
        multipoleIntegralCut χ N β lam M (ε₀ * truncationScale p₀ β lam) S := by
    rw [← mul_assoc, ← mul_pow]
    congr 2
    field_simp
  rw [heq]
  exact mul_le_mul_of_nonneg_left
    (RouteChain.multipoleIntegralCut_le hχ hlam N β M _ S) (by positivity)

/-- The normalization sandwich loses at most `2^|S|` in the lower transfer.
proof of Proposition 4.23, using (4.13). -/
theorem zeroPartitionFunction_transfer_half (hχ : IsMollifier χ) (hβ : 2 < β)
    (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hN : 1 ≤ N)
    (hcut : 1 / 2 * dipoleConstant χ β * lam ^ (2 - β) ≤
      cutoffDipoleNormalization χ N p₀ β lam ε₀) (S : Finset ℕ) :
    (1 / 2 : ℝ) ^ S.card * zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ≤
      multipolePartitionFunction χ N β lam M S := by
  have hfull := dipoleNormalization_pos hχ hlam β hN
  have hratio : (1 / 2 : ℝ) ≤
      cutoffDipoleNormalization χ N p₀ β lam ε₀ / dipoleNormalization χ N β lam := by
    rw [le_div_iff₀ hfull]
    calc 1 / 2 * dipoleNormalization χ N β lam ≤
        1 / 2 * (lam ^ (2 - β) * dipoleConstant χ β) :=
          mul_le_mul_of_nonneg_left (dipoleNormalization_le hχ hβ hlam N) (by norm_num)
      _ ≤ cutoffDipoleNormalization χ N p₀ β lam ε₀ := by nlinarith [hcut]
  have hzero : 0 ≤ zeroPartitionFunction χ N p₀ β lam M ε₀ {S} := by
    simp only [zeroPartitionFunction, Finset.prod_singleton]
    exact (modelHyp_zero hχ hlam β hε₀ hN).modelPartitionFunction_nonneg M lam S
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hratio S.card) hzero).trans
    (zeroPartitionFunction_transfer hχ hlam hε₀ hN S)

/-- The two bounds for the untruncated normalizer, with the lower bound
transferred from the truncated zero model. See the proof of Proposition 4.23. -/
theorem multipolePartitionFunction_two_sided (χ : ℂ → ℝ) (hχ : IsMollifier χ) (β : ℝ)
    (hβ : 2 < β) :
    ∀ k : ℕ, 2 ≤ k → (k : ℕ∞) ≤ pStar β → ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ S : Finset ℕ, S ⊆ Finset.range N → S.card = k →
            lam ^ (2 * (k - 1)) / (C * (N : ℝ) ^ (k - 1)) ≤
                multipolePartitionFunction χ N β lam M S ∧
              multipolePartitionFunction χ N β lam M S ≤
                C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1) := by
  intro k hk hkp
  refine ⟨21, by norm_num, fun M hM => ?_⟩
  obtain ⟨Cl, hCl, hl⟩ := BoundedLowerEps.zeroPartitionFunction_two_sided hχ hβ hk hkp
    (M := M) (by linarith)
  obtain ⟨lam₁, hlam₁, hlam₁1, hl⟩ := hl (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨lam₂, hlam₂, hcut⟩ := lem411_lower hχ hβ (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨Cu, hCu, hu⟩ := multipoleIntegral_le hχ hβ (by omega : 1 ≤ k) hkp
    (M := M) (by linarith)
  let Z := dipoleConstant χ β
  have hZ : 0 < Z := dipoleConstant_pos hχ hβ
  let C := max (Cu * (2 / Z) ^ k) (Cl * 2 ^ k)
  have hC : 0 < C := lt_max_of_lt_left (by positivity)
  refine ⟨C, hC, min lam₁ lam₂, lt_min hlam₁ hlam₂,
    (min_le_left _ _).trans hlam₁1, fun lam hlam hlt => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hl 0 lam hlam (hlt.trans_le (min_le_left _ _))
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1
    (hcut 0 lam hlam (hlt.trans_le (min_le_right _ _)))
  obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.1 (eventually_half_le_dipoleNormalization hχ hβ hlam)
  refine ⟨max (max N₁ N₂) (max N₃ 1), fun N hN S _ hS => ?_⟩
  have hN1 : 1 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNk : 0 < (N : ℝ) ^ (k - 1) := by positivity
  have hΛ : 0 ≤ lam ^ (2 * (k - 1)) := by positivity
  constructor
  · have hlo := (hN₁ N ((le_max_left _ _).trans ((le_max_left _ _).trans hN)) S hS).1
    have htr := zeroPartitionFunction_transfer_half (M := M) (p₀ := 0) hχ hβ hlam
      (show (0 : ℝ) < 1 / 2 by norm_num) hN1
      (hN₂ N ((le_max_right _ _).trans ((le_max_left _ _).trans hN))) S
    rw [hS] at htr
    have hscaled := mul_le_mul_of_nonneg_left hlo (show 0 ≤ (1 / 2 : ℝ) ^ k by positivity)
    have heq : (1 / 2 : ℝ) ^ k * (lam ^ (2 * (k - 1)) / (Cl * (N : ℝ) ^ (k - 1))) =
        lam ^ (2 * (k - 1)) / (Cl * 2 ^ k * (N : ℝ) ^ (k - 1)) := by
      rw [div_pow, one_pow]
      field_simp
    rw [heq] at hscaled
    exact (div_le_div_of_nonneg_left hΛ (by positivity)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hNk.le)).trans (hscaled.trans htr)
  · rw [multipolePartitionFunction_eq_multipoleIntegral hχ hlam β M hN1 S, hS]
    have hCN := hN₃ N ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
    have hA : (N : ℝ) * (Z / 2) * lam ^ (2 - β) ≤ N * dipoleNormalization χ N β lam := by
      calc _ = (N : ℝ) * (1 / 2 * Z * lam ^ (2 - β)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hCN hNp.le
    have hI := hu lam hlam N S hS
    have hp : (lam ^ (2 - β)) ^ k = lam ^ ((2 - β) * k) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
    rw [← hp] at hI
    have hi0 : 0 ≤ multipoleIntegral χ N β lam M S := by
      rw [multipoleIntegral_eq_toReal_lintegral hχ hlam N β M S]
      exact ENNReal.toReal_nonneg
    exact (gate_upper_algebra (by omega) hNp (Real.rpow_pos_of_pos hlam _) hZ hA hI hi0).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hΛ) hNk.le)

end MultipoleBKT.LowerBound.RouteBounded

end
