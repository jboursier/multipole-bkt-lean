/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.TypeTwo
public import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeTwoCount.Sharp

/-!
# Lemma 5.41 for `β ≥ 4`

The paper: Lemma 5.41 (2),
(5.140), and the final series bound.

Use the sharp leaf gain and ordered core, enumerate the actual component
partitions, cancel the dipole normalization power, and sum the written
size series with `sourceEta`. Its ratio is at most one half for small `λ`.
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open MeasureTheory Finset MultipoleIntegral Filter
open scoped ENNReal

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ : ℝ}

/-- Cutoff logarithm bound retained for the critical type-three radial integral.
The paper: (5.119).
The type-(2,1) series instead uses `sourceEta` and `sourceEta_le_self`. -/
theorem eta_le_high (hβ4 : 4 ≤ β) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hε₀ : 0 < ε₀)
    (hε₀1 : ε₀ ≤ 1) :
    lam ^ 2 * (1 + Real.log (cutoff p₀ β lam ε₀ / lam)) ≤ (2 * p₀ + 2) * lam := by
  have hcut : cutoff p₀ β lam ε₀ = cutoff p₀ 4 lam ε₀ := by
    unfold cutoff
    rw [truncationScale_of_ge_rpow hβ4, truncationScale_of_ge_rpow (β := 4) le_rfl]
  rw [hcut]
  calc
    _ ≤ (2 * p₀ + 2) * sourceEta 4 lam := by
      simpa only [ite_true] using
        cutoff_eta_le_source (p₀ := p₀) (β := 4) le_rfl hlam hε₀ hε₀1
    _ ≤ (2 * p₀ + 2) * lam :=
      mul_le_mul_of_nonneg_left (sourceEta_le_self hlam hlam1) (by positivity)

/-- Normalization of the sharp partition series before its written summation. -/
private theorem high_source_normalized_series_le {K c₀ t y : ℝ} (hK : 0 < K)
    (hc₀0 : 0 < c₀) (hlam : 0 < lam) (hy : 0 ≤ y)
    (hyy₀ : y ≤ Real.exp t / (c₀ * lam ^ (2 - β)))
    (hw : (Real.exp 1 * K * Real.exp t / c₀) * sourceEta β lam ≤ 1 / 2)
    (N n : ℕ) :
    ∑ m ∈ range n, (if p₀ < m + 1 then
      (N : ℝ) * ((m + 1) ^ (m + 1 - 2) : ℕ) *
        (K ^ (m + 1) * lam ^ ((2 - β) * (m + 1)) * lam ^ (2 * p₀) *
          sourceEta β lam ^ (m + 1 - (p₀ + 1))) else 0) /
        (m + 1).factorial * y ^ (m + 1) ≤
      (Real.exp 1 * K * Real.exp t / c₀) ^ (p₀ + 1) * 2 ^ p₀ * 4 * N * lam ^ (2 * p₀) := by
  let z := Real.exp 1 * K * Real.exp t / c₀
  let y₀ := Real.exp t / (c₀ * lam ^ (2 - β))
  have hz0 : 0 < z := by dsimp [z]; positivity
  have hη0 : 0 ≤ sourceEta β lam := by unfold sourceEta; split_ifs <;> positivity
  calc
    _ ≤ ∑ m ∈ range n, (N : ℝ) * (if p₀ < m + 1 then
        ((m + 1 : ℕ) : ℝ) * lam ^ (2 * p₀) * z ^ (m + 1) *
          sourceEta β lam ^ (m + 1 - (p₀ + 1)) else 0) := by
      apply sum_le_sum
      intro m _
      split_ifs with hm
      · calc
          _ ≤ ((N : ℝ) * ((m + 1) ^ (m + 1 - 2) : ℕ) *
              (K ^ (m + 1) * lam ^ ((2 - β) * (m + 1)) * lam ^ (2 * p₀) *
                sourceEta β lam ^ (m + 1 - (p₀ + 1)))) /
              (m + 1).factorial * y₀ ^ (m + 1) := by
                apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hyy₀ _)
                positivity
          _ ≤ _ := by
            simpa only [Nat.cast_add, Nat.cast_one] using
              high_source_term_le (p₀ := p₀) (m := m + 1) (N := N)
                (β := β) (lam := lam) (C := K) (c₀ := c₀) (t := t) hm hlam hK hc₀0
      · simp only [zero_div, zero_mul, mul_zero, le_refl]
    _ = (N : ℝ) * ∑ m ∈ range n, (if p₀ < m + 1 then
        ((m + 1 : ℕ) : ℝ) * lam ^ (2 * p₀) * z ^ (m + 1) *
          sourceEta β lam ^ (m + 1 - (p₀ + 1)) else 0) := by rw [mul_sum]
    _ ≤ (N : ℝ) * (lam ^ (2 * p₀) * z ^ (p₀ + 1) * 2 ^ p₀ * 4) :=
      mul_le_mul_of_nonneg_left (high_source_series_le hz0.le hw n) (Nat.cast_nonneg N)
    _ = _ := by ring

/-- **Lemma 5.41 (2)** (Lemma 5.41, `β ≥ 4`, the paper): for every
`t ≥ 1` there is `C` (depending on `χ, β, M, p₀, t` only) such that for every `ε₀ ∈ (0, 1]`, for
`λ` small (depending also on `ε₀`) and `N` large, for every `n`,
`(N/n)ⁿ Z^{(2,1)}_{bad,n} e^{tn} / (N C_{β,λ,ε₀})ⁿ ≤ e^{C N λ^{2p₀}}`, written multiplicatively. -/
theorem lemma_5_41_high (hχ : IsMollifier χ) (hp₀ : 1 ≤ p₀) (hβ4 : 4 ≤ β) (hM : 0 ≤ M) :
    ∀ t : ℝ, 1 ≤ t → ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ ≤ 1 → ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
        typeTwoOnePartitionFunction χ p₀ β lam M ε₀ N n ≤
          ENNReal.ofReal ((N * truncatedDipoleNormalization χ N β lam
              (ε₀ * truncationScale p₀ β lam)) ^ n * ((n : ℝ) / N) ^ n *
            (Real.exp (-(t * n)) * Real.exp (C * N * lam ^ (2 * p₀)))) := by
  intro t ht
  have hβ : 2 < β := by linarith
  have hZ := dipoleConstant_pos hχ hβ
  set c₀ := 1 / 2 * dipoleConstant χ β with hc₀
  have hc₀0 : 0 < c₀ := by positivity
  obtain ⟨K, hK, hsharp⟩ := typeTwoOnePartitionFunction_le_exp_high_source (p₀ := p₀) hχ hβ4 hM
  set z := Real.exp 1 * K * Real.exp t / c₀ with hz
  have hz0 : 0 < z := by positivity
  refine ⟨z ^ (p₀ + 1) * 2 ^ p₀ * 4, by positivity, fun ε₀ hε₀ hε₀1 => ?_⟩
  obtain ⟨lam₁, hlam₁, hnorm⟩ := eventually_half_le_normalization hχ hβ hp₀ hε₀ hε₀1
  obtain ⟨lam₂, hlam₂, hcut⟩ := eventually_lam_le_cutoff hβ hp₀ hε₀
  set lam₃ := 1 / (2 * z) with hlam₃d
  have hlam₃ : 0 < lam₃ := by positivity
  refine ⟨min (min lam₁ lam₂) lam₃, lt_min (lt_min hlam₁ hlam₂) hlam₃, fun lam hlam hlt' => ?_⟩
  have hl1 : lam < lam₁ := hlt'.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hl2 : lam < lam₂ := hlt'.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hl3 : lam < lam₃ := hlt'.trans_le (min_le_right _ _)
  obtain ⟨hlam1, hlh⟩ := hcut lam hlam hl2
  have hη0 : 0 ≤ sourceEta β lam := by unfold sourceEta; split_ifs <;> positivity
  have hw : z * sourceEta β lam ≤ 1 / 2 := by
    calc
      _ ≤ z * lam := mul_le_mul_of_nonneg_left (sourceEta_le_self hlam hlam1) hz0.le
      _ ≤ z * lam₃ := by gcongr
      _ = 1 / 2 := by rw [hlam₃d]; field_simp
  filter_upwards [hnorm lam hlam hl1, eventually_ge_atTop 1] with N hNC hN1 n
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have hlb : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  set Cε := truncatedDipoleNormalization χ N β lam (ε₀ * truncationScale p₀ β lam)
  have hCε : c₀ * lam ^ (2 - β) ≤ Cε := hNC
  have hCε0 : 0 < Cε := lt_of_lt_of_le (by positivity) hCε
  set y := Real.exp t / Cε
  have hy : 0 < y := by positivity
  refine (hsharp lam hlam ε₀ hε₀ hε₀1 hlh N n y hy).trans
    (ENNReal.ofReal_le_ofReal ?_)
  -- the prefactor
  have hpre : (n.factorial : ℝ) / y ^ n ≤
      (N * Cε) ^ n * ((n : ℝ) / N) ^ n * Real.exp (-(t * n)) := by
    have hnn : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    have heq : (N * Cε) ^ n * ((n : ℝ) / N) ^ n * Real.exp (-(t * n)) = (n : ℝ) ^ n / y ^ n := by
      rw [show -(t * n) = n * (-t) by ring, Real.exp_nat_mul, Real.exp_neg, ← mul_pow, ← mul_pow,
        ← div_pow]
      congr 1
      rw [show y = Real.exp t / Cε from rfl]
      field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right hnn (by positivity)
  -- the series
  set y₀ := Real.exp t / (c₀ * lam ^ (2 - β))
  have hyy₀ : y ≤ y₀ := div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hCε
  have hseries := high_source_normalized_series_le (p₀ := p₀) hK hc₀0 hlam hy.le hyy₀ hw N n
  calc (n.factorial : ℝ) / y ^ n * Real.exp (∑ m ∈ Finset.range n,
        (if p₀ < m + 1 then
          (N : ℝ) * ((m + 1) ^ (m + 1 - 2) : ℕ) *
            (K ^ (m + 1) * lam ^ ((2 - β) * (m + 1)) * lam ^ (2 * p₀) *
              sourceEta β lam ^ (m + 1 - (p₀ + 1))) else 0) /
          (m + 1).factorial * y ^ (m + 1))
      ≤ ((N * Cε) ^ n * ((n : ℝ) / N) ^ n * Real.exp (-(t * n))) *
          Real.exp (z ^ (p₀ + 1) * 2 ^ p₀ * 4 * N * lam ^ (2 * p₀)) :=
        mul_le_mul hpre (Real.exp_le_exp.2 hseries) (Real.exp_pos _).le
          (by positivity)
    _ = _ := by ring

end BadPointTypes

end MultipoleBKT

end
