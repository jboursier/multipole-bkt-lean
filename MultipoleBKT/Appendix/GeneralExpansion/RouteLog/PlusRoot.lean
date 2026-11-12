/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansion.RouteLog.WeightedRoot
public import MultipoleBKT.Appendix.GeneralExpansion.RouteLog.RootMoments

/-!
# The frozen multipole root error through logarithmic integration

See (A.43), (A.44)
and (A.45). The two bad-point contributions use the
zeroth and first logarithmic moments. The cap is normalized separately.
-/

@[expose] public section

namespace MultipoleBKT.GeneralExpansion

open MeasureTheory Set Finset Metric
open scoped ENNReal
open MultipoleIntegral UpperBound MultipoleIntegralZ

variable {χ : ℂ → ℝ} {β M : ℝ}

/-- The consumed root interface, proved by the actual root geometry and
its three logarithmic radial regimes. -/
theorem lintegral_plus_root_log_le (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 1 ≤ k)
    (hM : 0 ≤ M) (p₀ : ℕ) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ (ε₀ lam : ℝ), 0 < lam → lam ≤ ε₀ → ε₀ ≤ 1 →
      (3 : ℝ) ^ pBeta p₀ β ≤ M → ∀ (N : ℕ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
      badPointsOn p₀ β lam M ε₀ V Z = V → ∀ (S : Finset ℕ), S.card = k → ∀ i₀ : S,
        ∫⁻ c : S → ℂ × ℂ, connInd M lam c *
            ((∏ i, cutWeight χ β lam (ε₀ * truncationScale p₀ β lam) ((c i).1 - (c i).2)) *
              rootZ p₀ β lam M ε₀ V Z ((c i₀).1 - (c i₀).2) (c i₀).2) ≤
          ENNReal.ofReal (C₁ * ε₀ ^ (tailSigma p₀ β k * k - 2) * N *
              (lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ)) +
            C₂ * ε₀ ^ (alphaExponent β * k) * V.card * lam ^ ((2 - β) * k)) := by
  classical
  obtain ⟨C₀, hC₀, hcap⟩ := moment_product_cap_le hβ p₀ hk
  obtain ⟨C₁, hC₁, hbad₀⟩ := moment_product_bad_le hβ p₀ hk 0
  obtain ⟨C₂, hC₂, hbad₁⟩ := moment_product_bad_le hβ p₀ hk 1
  let K := 2 * Real.pi * Real.exp (β * MultipoleIntegral.kernelConst χ)
  let B := 4 * Real.pi * M ^ 2
  let D := 128 * Real.pi * (1 + Real.log 17)
  let A := ((k ^ k : ℕ) : ℝ) * B ^ (k - 1) * K ^ k
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hD : 0 ≤ D := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 17 by norm_num)
    dsimp only [D]
    positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨A * C₀, A * (B * C₁ + D * C₂), by positivity, by positivity,
    fun eps lam hlam hle heps1 hM3 N V Z hV S hS i₀ => ?_⟩
  have heps : 0 < eps := hlam.trans_le hle
  let R := truncationScale p₀ β lam
  let h := eps * R
  have hR : 0 < R := Appendix.truncationScale_pos hlam
  have hlh : lam ≤ h := hle.trans
    (le_mul_of_one_le_right heps.le (Appendix.one_le_truncationScale hβ hlam (hle.trans heps1)))
  have hh : 0 < h := hlam.trans_le hlh
  let m₀ := RouteLog.radialLogMoment (4 - β) lam h 0
  let m₁ := RouteLog.radialLogMoment (4 - β) lam h 1
  have hm₀ : 0 ≤ m₀ := radialLogMoment_nonneg _ _ hlam hlh
  have hm₁ : 0 ≤ m₁ := radialLogMoment_nonneg _ _ hlam hlh
  have hcard : Fintype.card S = k := by rw [Fintype.card_coe, hS]
  have hedge : ∫⁻ w, cutWeight χ β lam h w *
      ENNReal.ofReal (4 * Real.pi * (M * max ‖w‖ lam) ^ 2) ≤
      ENNReal.ofReal (B * K * m₀) := by
    have he : ∀ w : ℂ, cutWeight χ β lam h w *
        ENNReal.ofReal (4 * Real.pi * (M * max ‖w‖ lam) ^ 2) =
        ENNReal.ofReal B * (cutWeight χ β lam h w *
          ENNReal.ofReal (max ‖w‖ lam ^ 2 * (1 + Real.log (h / max ‖w‖ lam)) ^ 0)) := by
      intro w
      simp only [pow_zero, mul_one]
      rw [show 4 * Real.pi * (M * max ‖w‖ lam) ^ 2 = B * max ‖w‖ lam ^ 2 by
        dsimp only [B]
        ring, ENNReal.ofReal_mul hB]
      ring
    simp_rw [he]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul' le_rfl (lintegral_cutWeight_log_le hχ (by linarith) hlam hlh 0)).trans
      (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul hB]
    congr 1
    ring
  have hroot := lintegral_rootZ_moments_le hχ (by linarith) hlam hlh hM3 hV
  have hgeom := lintegral_rooted_weighted_power_le (ι := S) hM hlam.le i₀
    (cutWeight χ β lam h) (measurable_cutWeight hχ hlam β h)
    (rootZ p₀ β lam M eps V Z) (measurable_rootZ p₀ β lam M eps V Z)
  rw [hcard] at hgeom
  have hmoment : (∫⁻ c : S → ℂ × ℂ, connInd M lam c *
      ((∏ i, cutWeight χ β lam h ((c i).1 - (c i).2)) *
        rootZ p₀ β lam M eps V Z ((c i₀).1 - (c i₀).2) (c i₀).2)) ≤
      ENNReal.ofReal (A * ((N / h ^ 2) * m₀ ^ k +
        B * V.card * (m₀ * m₀ ^ (k - 1)) + D * V.card * (m₁ * m₀ ^ (k - 1)))) := by
    refine hgeom.trans ?_
    calc
      _ ≤ ((k ^ k : ℕ) : ℝ≥0∞) *
          (ENNReal.ofReal (B * K * m₀) ^ (k - 1) *
            ENNReal.ofReal (K * ((N / h ^ 2 + B * V.card) * m₀ + D * V.card * m₁))) := by
        apply mul_le_mul' le_rfl
        apply mul_le_mul'
        · exact pow_le_pow_left' hedge (k - 1)
        · convert hroot using 1
          congr 1
          dsimp only [K, B, D, m₀, m₁, h, R]
          ring
      _ = _ := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        dsimp only [A]
        rw [mul_pow, mul_pow, show K ^ k = K * K ^ (k - 1) by
          rw [← pow_succ', Nat.sub_add_cancel hk]]
        have he : m₀ ^ k = m₀ * m₀ ^ (k - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hk]
        rw [he]
        ring
  refine hmoment.trans (ENNReal.ofReal_le_ofReal ?_)
  have hc := hcap eps lam hlam hle heps1
  have hb₀ := hbad₀ eps lam hlam hle heps1
  have hb₁ := hbad₁ eps lam hlam hle heps1
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hV0 : (0 : ℝ) ≤ V.card := Nat.cast_nonneg V.card
  calc
    _ ≤ A * ((N / h ^ 2) * (C₀ * eps ^ (tailSigma p₀ β k * k) * lam ^ ((2 - β) * k)) +
        B * V.card * (C₁ * eps ^ (alphaExponent β * k) * lam ^ ((2 - β) * k)) +
        D * V.card * (C₂ * eps ^ (alphaExponent β * k) * lam ^ ((2 - β) * k))) := by
      gcongr
    _ = _ := by
      have he := cutoff_cap_scaling (p₀ := p₀) (β := β) (d := tailSigma p₀ β k * k) hlam heps
      change eps ^ (tailSigma p₀ β k * k) / h ^ 2 =
        eps ^ (tailSigma p₀ β k * k - 2) * R ^ (-2 : ℝ) at he
      simp only [div_eq_mul_inv] at he ⊢
      calc
        _ = A * C₀ * N * lam ^ ((2 - β) * k) *
            (eps ^ (tailSigma p₀ β k * k) * (h ^ 2)⁻¹) +
            A * (B * C₁ + D * C₂) * eps ^ (alphaExponent β * k) * V.card *
              lam ^ ((2 - β) * k) := by ring
        _ = _ := by rw [he]; ring

end MultipoleBKT.GeneralExpansion

end
