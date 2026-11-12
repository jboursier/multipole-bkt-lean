/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.RouteChain.BadNeighborhood

/-!
# Absorbing the weighted loss

See (A.15),
(A.16). Extract the common scale before subtracting.
The condition `|V_bad| ≤ N` leaves a positive fraction for small `λ`.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegral.RouteChain

open MeasureTheory Set Finset UpperBound MultipoleIntegralZ
open scoped ENNReal Classical

/-- The coefficient of the explicit weighted chain lower bound. -/
noncomputable def lowerCoefficient (β : ℝ) (k : ℕ) : ℝ :=
  ((4 : ℝ) ^ (-β)) ^ k * (Real.pi / 256) ^ (2 * k - 1) / 4

/-- The coefficient of the full-event weighted bad-neighbourhood upper bound. -/
noncomputable def lossCoefficient (χ : ℂ → ℝ) (β M : ℝ) (k : ℕ) : ℝ :=
  k * (2 * Real.pi * (2 * M + 2) ^ 2) * (256 * Real.pi) ^ (k - 1) *
    (Real.exp (β * kernelConst χ) * (4 * Real.pi)) ^ k

theorem lowerCoefficient_pos (β : ℝ) (k : ℕ) : 0 < lowerCoefficient β k := by
  unfold lowerCoefficient
  positivity

/-- The endpoint-ball scale in (A.15). -/
theorem lower_scale {β lam : ℝ} (hlam : 0 < lam) {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    (((4 * lam) ^ (-β)) ^ k) * (N / 4) * (Real.pi * (lam / 16) ^ 2) ^ (2 * k - 1) =
      lowerCoefficient β k * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by
  have h4 : (4 * lam) ^ (-β) = (4 : ℝ) ^ (-β) * lam ^ (-β) :=
    Real.mul_rpow (by norm_num) hlam.le
  have hv : Real.pi * (lam / 16) ^ 2 = (Real.pi / 256) * lam ^ 2 := by ring
  rw [h4, hv, mul_pow, mul_pow]
  have hs := rpow_neg_pow_mul_sq_pow (β := β) hlam hk
  calc _ = lowerCoefficient β k * N * ((lam ^ (-β)) ^ k * (lam ^ 2) ^ (2 * k - 1)) := by
          unfold lowerCoefficient
          ring
    _ = _ := by rw [hs]; ring

/-- The spatial and radial factors of (A.16) have the paper's stated power. -/
theorem loss_scale (χ : ℂ → ℝ) {β lam M : ℝ} (hlam : 0 < lam) {k : ℕ} (hk : 1 ≤ k) (v : ℝ) :
    k * (2 * v * Real.pi * ((2 * M + 2) * lam) ^ 2) *
        (256 * Real.pi * lam ^ 2) ^ (k - 1) *
        ((Real.exp (β * kernelConst χ) * lam ^ (-β)) * (4 * Real.pi * lam ^ 2)) ^ k =
      lossCoefficient χ β M k * v * lam ^ 2 *
        (lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) := by
  have he : (Real.exp (β * kernelConst χ) * lam ^ (-β)) * (4 * Real.pi * lam ^ 2) =
      (Real.exp (β * kernelConst χ) * (4 * Real.pi)) * lam ^ (-β) * lam ^ 2 := by ring
  rw [he, mul_pow, mul_pow, mul_pow]
  rw [← rpow_neg_pow_mul_sq_pow (β := β) hlam hk]
  have hp : (lam ^ 2) ^ (2 * k - 1) = (lam ^ 2) ^ (k - 1) * (lam ^ 2) ^ k := by
    rw [← pow_add, show k - 1 + k = 2 * k - 1 by omega]
  rw [hp]
  unfold lossCoefficient
  ring

/-- (A.15) in the common scale used in the subtraction. -/
theorem support_mass_scaled {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β lam : ℝ}
    (hβ : 0 ≤ β) (hlam : 0 < lam) {k N : ℕ} (hk : 1 ≤ k) {S : Finset ℕ}
    (σ : S ≃ Fin k) (hN : 4 * (5 * k * lam) ≤ Real.sqrt N) :
    ENNReal.ofReal (lowerCoefficient β k * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) ≤
      ∫⁻ c, supportWeight χ N β lam σ c := by
  have hcard : Fintype.card S = k := by simpa using Fintype.card_congr σ
  have h := support_mass_lower hχ hβ hlam σ (σ.symm ⟨0, hk⟩) (by simp) N hN
  rw [hcard, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)] at h
  convert h using 1
  congr 1
  rw [← lower_scale (β := β) hlam hk N]
  ring

/-- The positive weighted chain mass exported for the limit argument with one fixed dipole
at Proposition 4.23. -/
theorem chain_weighted_integral_pos {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β lam : ℝ}
    (hβ : 0 ≤ β) (hlam : 0 < lam) {k N : ℕ} (hk : 1 ≤ k) (hNpos : 0 < N)
    {S : Finset ℕ} (σ : S ≃ Fin k) (hN : 4 * (5 * k * lam) ≤ Real.sqrt N) :
    0 < ∫⁻ c, supportWeight χ N β lam σ c := by
  apply lt_of_lt_of_le _ (support_mass_scaled hχ hβ hlam hk σ hN)
  apply ENNReal.ofReal_pos.mpr
  have := lowerCoefficient_pos β k
  positivity

/-- (A.16) in the common scale used in the subtraction. -/
theorem weighted_bad_scaled {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β lam M ε₀ : ℝ}
    (hβ : 0 ≤ β) (hlam : 0 < lam) (hM : 0 ≤ M) {k N p₀ : ℕ} (hk : 1 ≤ k)
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) {S : Finset ℕ} (σ : S ≃ Fin k) :
    ∫⁻ c, badWeight χ N p₀ β lam M ε₀ V Z σ c ≤
      ENNReal.ofReal (lossCoefficient χ β M k * V.card * lam ^ 2 *
        (lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)))) := by
  have hcard : Fintype.card S = k := by simpa using Fintype.card_congr σ
  have h := weighted_bad_neighborhood_le (N := N) (p₀ := p₀) (ε₀ := ε₀) (V := V) (Z := Z) hχ hβ hlam hM σ
  rw [hcard] at h
  have hn : (k : ℝ≥0∞) = ENNReal.ofReal (k : ℝ) := by simp
  rw [hn, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)] at h
  exact h.trans_eq (congrArg ENNReal.ofReal (loss_scale χ hlam hk V.card))

/-- Subtract the weighted bad-neighbourhood estimate from the chain mass.
The smallness condition is numerical and independent of `N`, `V`, and `Z`. -/
theorem good_mass_lower {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β lam M ε₀ : ℝ}
    (hβ : 0 ≤ β) (hlam : 0 < lam) (hM : 0 ≤ M) {k N p₀ : ℕ} (hk : 1 ≤ k)
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) {S : Finset ℕ} (σ : S ≃ Fin k)
    (hN : 4 * (5 * k * lam) ≤ Real.sqrt N)
    (hsmall : lossCoefficient χ β M k * lam ^ 2 ≤ lowerCoefficient β k / 2) :
    ENNReal.ofReal (lowerCoefficient β k / 2 * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) ≤
      ∫⁻ c, {c | ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (c i)}.indicator
        (supportWeight χ N β lam σ) c := by
  let scale := lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))
  have hs : 0 ≤ scale := by positivity
  have hv : (V.card : ℝ) ≤ N := by
    have hh := Finset.card_le_univ V
    rw [Fintype.card_fin] at hh
    exact_mod_cast hh
  have hB := weighted_bad_scaled (p₀ := p₀) (ε₀ := ε₀) hχ hβ hlam hM hk V Z σ
  have hc : 0 ≤ lossCoefficient χ β M k := by unfold lossCoefficient; positivity
  have hb : lossCoefficient χ β M k * V.card * lam ^ 2 * scale ≤
      lowerCoefficient β k / 2 * N * scale := by
    have h1 := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    have h2 := mul_le_mul_of_nonneg_left hv (mul_nonneg hc (sq_nonneg lam))
    have h3 : lossCoefficient χ β M k * V.card * lam ^ 2 ≤ lowerCoefficient β k / 2 * N := by nlinarith
    exact mul_le_mul_of_nonneg_right h3 hs
  have hBad : (∫⁻ c, badWeight χ N p₀ β lam M ε₀ V Z σ c) ≤
      ENNReal.ofReal (lowerCoefficient β k / 2 * N * scale) := hB.trans (ENNReal.ofReal_le_ofReal hb)
  have hTotal := support_mass_scaled hχ hβ hlam hk σ hN
  rw [← weighted_subtraction (p₀ := p₀) (M := M) (ε₀ := ε₀) (V := V) (Z := Z) χ hχ hlam σ] at hTotal
  have ht : ENNReal.ofReal (lowerCoefficient β k / 2 * N * scale) +
      ENNReal.ofReal (lowerCoefficient β k / 2 * N * scale) ≤
        (∫⁻ c, {c | ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (c i)}.indicator
          (supportWeight χ N β lam σ) c) + ENNReal.ofReal (lowerCoefficient β k / 2 * N * scale) := by
    have h0 : 0 ≤ lowerCoefficient β k / 2 * N * scale := by
      have := (lowerCoefficient_pos β k).le
      positivity
    rw [← ENNReal.ofReal_add h0 h0]
    have he : lowerCoefficient β k / 2 * N * scale + lowerCoefficient β k / 2 * N * scale =
        lowerCoefficient β k * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by dsimp [scale]; ring
    rw [he]
    exact hTotal.trans (add_le_add le_rfl hBad)
  have hout := (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp ht
  convert hout using 1
  congr 1
  dsimp [scale]
  ring

end MultipoleBKT.MultipoleIntegral.RouteChain

end
