/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.DipoleConstant
public import MultipoleBKT.Frozen.TruncationScale

/-!
# The normalization `C_{β,λ,ε₀}` of §5

The partition functions of the bad points are normalized by `(N C_{β,λ,ε₀})^{n}`, with
`C_{β,λ,ε₀} = (1/N) ∫_{Λ²} e^{β g_λ(x - y)} 𝟙_{|x - y| ≤ ε₀ R̄} dx dy` (`truncatedDipoleNormalization` with
`R = ε₀ R̄_{β,λ}`). The lemmas of Sections 5.12–5.14 use only its lower bound (4.12): `C_{β,λ,ε₀} ≥ 𝒵_β λ^{2-β} / 2` for `λ` small and `N` large
(`eventually_half_le_normalization`; the paper's statements omit "λ small enough", which is needed for this lower bound).

`normalized_le_of_le` is the elementary step from a bound `Z ≤ (A n)^n Y` to the paper's
normalized form `(N/n)^n Z / (N C)^n ≤ (A/c)^n Y` once `C ≥ c > 0` (used with `A = κ λ^{2-β}`,
`c = 𝒵_β λ^{2-β} / 2`).
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open Filter Topology
open scoped ENNReal

/-- `x^a → 0` as `x → 0⁺` for `a > 0`. -/
theorem tendsto_rpow_nhdsGT_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => x ^ a) (𝓝[>] 0) (𝓝 0) := by
  have h : ContinuousAt (fun x : ℝ => x ^ a) 0 := Real.continuousAt_rpow_const 0 a (Or.inr ha.le)
  have h0 : (0 : ℝ) ^ a = 0 := Real.zero_rpow ha.ne'
  rw [ContinuousAt, h0] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- **The lower bound (4.12)** on `C_{β,λ,ε₀}`, for `β > 2`,
`p₀ ≥ 1`, `ε₀ ∈ (0, 1]`: for `λ` small enough, `C_{β,λ,ε₀} ≥ 𝒵_β λ^{2-β} / 2` for all large
`N`. -/
theorem eventually_half_le_normalization {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β : ℝ} (hβ : 2 < β)
    {p₀ : ℕ} (hp₀ : 1 ≤ p₀) {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∀ᶠ N : ℕ in atTop,
      1 / 2 * dipoleConstant χ β * lam ^ (2 - β) ≤
        truncatedDipoleNormalization χ N β lam (ε₀ * truncationScale p₀ β lam) := by
  have hZ := dipoleConstant_pos hχ hβ
  set K : ℝ := 4 * Real.pi / ((β - 2) * dipoleConstant χ β)
  have hK : 0 < K := by
    have : 0 < β - 2 := by linarith
    positivity
  -- the exponent `a` with `R̄ = λ^{-a}`
  set a : ℝ := if β < 4 then (β - 2) / (4 - β) else 2 * p₀ with ha_def
  have ha : 0 < a := by
    rw [ha_def]
    split_ifs with h4
    · exact div_pos (by linarith) (by linarith)
    · have : (1 : ℝ) ≤ p₀ := by exact_mod_cast hp₀
      linarith
  have hR : ∀ lam : ℝ, 0 < lam → truncationScale p₀ β lam = lam ^ (-a) := by
    intro lam hlam
    unfold truncationScale
    rw [ha_def]
    split_ifs with h4
    · rw [criticalScale, ite_eq_left h4, ENNReal.toReal_ofReal (Real.rpow_nonneg hlam.le _)]
      congr 1
      ring
    · rw [show -(2 * (p₀ : ℝ)) = ((-(2 * (p₀ : ℤ)) : ℤ) : ℝ) by push_cast; ring,
        Real.rpow_intCast]
  -- the three smallness conditions hold near `0⁺`
  have h1 : ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam ^ (1 + a) < ε₀ / 2 :=
    (tendsto_rpow_nhdsGT_zero (by linarith)).eventually (gt_mem_nhds (by linarith))
  have h2 : ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam ^ (2 * a) < ε₀ ^ 2 / K :=
    (tendsto_rpow_nhdsGT_zero (by linarith)).eventually (gt_mem_nhds (by positivity))
  have h3 : ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam < 1 :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨u, hu, hsub⟩ := (h1.and (h2.and h3)).exists_mem
  obtain ⟨lam₀, hlam₀, hIoo⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hu
  refine ⟨lam₀, hlam₀, fun lam hlam hlt => ?_⟩
  obtain ⟨c1, c2, c3⟩ := hsub lam (hIoo ⟨hlam, hlt⟩)
  have hRlam := hR lam hlam
  set R := ε₀ * truncationScale p₀ β lam with hR_def
  have hpos : 0 < lam ^ (-a) := Real.rpow_pos_of_pos hlam _
  -- `2λ ≤ R`
  have hR2 : 2 * lam ≤ R := by
    rw [hR_def, hRlam]
    have e : lam ^ (1 + a) * lam ^ (-a) = lam := by
      rw [← Real.rpow_add hlam]
      simp
    nlinarith
  -- `R ≤ R_{β,λ}`
  have hRc : ENNReal.ofReal R ≤ criticalScale β lam := by
    unfold criticalScale
    split_ifs with h4
    · refine ENNReal.ofReal_le_ofReal ?_
      rw [hR_def, hRlam, ha_def, ite_eq_left h4]
      have : lam ^ (-((β - 2) / (4 - β))) = lam ^ (-(β - 2) / (4 - β)) := by
        congr 1
        ring
      rw [this]
      exact mul_le_of_le_one_left (Real.rpow_nonneg hlam.le _) hε₀1
    · exact le_top
  -- `R² > K`
  have hRK : K < R ^ 2 := by
    rw [hR_def, hRlam, mul_pow]
    have e : (lam ^ (-a)) ^ 2 * lam ^ (2 * a) = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hlam.le, ← Real.rpow_add hlam]
      norm_num
      ring_nf
      simp
    have hl2 : 0 < lam ^ (2 * a) := Real.rpow_pos_of_pos hlam _
    rw [lt_div_iff₀ hK] at c2
    have : K * lam ^ (2 * a) * (lam ^ (-a)) ^ 2 < ε₀ ^ 2 * (lam ^ (-a)) ^ 2 :=
      mul_lt_mul_of_pos_right (by linarith) (by positivity)
    calc K = K * ((lam ^ (-a)) ^ 2 * lam ^ (2 * a)) := by rw [e, mul_one]
      _ = K * lam ^ (2 * a) * (lam ^ (-a)) ^ 2 := by ring
      _ < ε₀ ^ 2 * (lam ^ (-a)) ^ 2 := this
  exact eventually_half_le_truncatedDipoleNormalization_of_le_criticalScale hχ hβ hlam c3.le hR2
    hRc hRK

/-- For `λ` small, `λ ≤ 1` and `λ ≤ ε₀ R̄_{β,λ}` (the standing assumption `λ ≤ ε₀ R̄` of §5,
Section 5.2). -/
theorem eventually_lam_le_cutoff {β : ℝ} (hβ : 2 < β) {p₀ : ℕ} (hp₀ : 1 ≤ p₀) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) : ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      lam ≤ 1 ∧ lam ≤ ε₀ * truncationScale p₀ β lam := by
  set a : ℝ := if β < 4 then (β - 2) / (4 - β) else 2 * p₀ with ha_def
  have ha : 0 < a := by
    rw [ha_def]
    split_ifs with h4
    · exact div_pos (by linarith) (by linarith)
    · have : (1 : ℝ) ≤ p₀ := by exact_mod_cast hp₀
      linarith
  have hR : ∀ lam : ℝ, 0 < lam → truncationScale p₀ β lam = lam ^ (-a) := by
    intro lam hlam
    unfold truncationScale
    rw [ha_def]
    split_ifs with h4
    · rw [criticalScale, ite_eq_left h4, ENNReal.toReal_ofReal (Real.rpow_nonneg hlam.le _)]
      congr 1
      ring
    · rw [show -(2 * (p₀ : ℝ)) = ((-(2 * (p₀ : ℤ)) : ℤ) : ℝ) by push_cast; ring,
        Real.rpow_intCast]
  have h1 : ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam ^ (1 + a) < ε₀ :=
    (tendsto_rpow_nhdsGT_zero (by linarith)).eventually (gt_mem_nhds hε₀)
  have h3 : ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam < 1 :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨u, hu, hsub⟩ := (h1.and h3).exists_mem
  obtain ⟨lam₀, hlam₀, hIoo⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hu
  refine ⟨lam₀, hlam₀, fun lam hlam hlt => ?_⟩
  obtain ⟨c1, c3⟩ := hsub lam (hIoo ⟨hlam, hlt⟩)
  refine ⟨c3.le, ?_⟩
  rw [hR lam hlam]
  have e : lam ^ (1 + a) * lam ^ (-a) = lam := by
    rw [← Real.rpow_add hlam]
    simp
  have hpos : 0 < lam ^ (-a) := Real.rpow_pos_of_pos hlam _
  nlinarith

/-- From an explicit bound to the normalized one: `(N/n)^n Z / (N C)^n ≤ (A/c)^n Y` when
`Z ≤ (A n)^n Y`, `C ≥ c > 0`, `N > 0` (for `n = 0` both sides reduce to `Z ≤ Y`). -/
theorem normalized_le_of_le {Z Y A c C N : ℝ} {n : ℕ} (hZ : Z ≤ (A * n) ^ n * Y)
    (hN : 0 < N) (hc : 0 < c) (hcC : c ≤ C) (hA : 0 ≤ A) (hY : 0 ≤ Y) :
    (N / n) ^ n * Z / (N * C) ^ n ≤ (A / c) ^ n * Y := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hZ
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hC : 0 < C := hc.trans_le hcC
  have hNC : 0 < (N * C) ^ n := pow_pos (mul_pos hN hC) n
  rw [div_le_iff₀ hNC]
  calc (N / n) ^ n * Z ≤ (N / n) ^ n * ((A * n) ^ n * Y) :=
        mul_le_mul_of_nonneg_left hZ (pow_nonneg (div_nonneg hN.le hn'.le) n)
    _ = (A * N) ^ n * Y := by
        rw [← mul_assoc, ← mul_pow]
        congr 2
        field_simp
    _ ≤ (A / c * (N * C)) ^ n * Y := by
        have h : A * N ≤ A / c * (N * C) := by
          rw [show A / c * (N * C) = A * N * (C / c) by field_simp]
          exact le_mul_of_one_le_right (by positivity) ((one_le_div hc).2 hcC)
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h n) hY
    _ = (A / c) ^ n * Y * (N * C) ^ n := by rw [mul_pow]; ring

/-- The multiplicative form of `normalized_le_of_le`: `Z ≤ (N C)^n (n/N)^n (A/c)^n Y` when
`Z ≤ (A n)^n Y`, `C ≥ c > 0`, `N > 0`. -/
theorem le_normalized_of_le {Z Y A c C N : ℝ} {n : ℕ} (hZ : Z ≤ (A * n) ^ n * Y)
    (hN : 0 < N) (hc : 0 < c) (hcC : c ≤ C) (hA : 0 ≤ A) (hY : 0 ≤ Y) :
    Z ≤ (N * C) ^ n * ((n : ℝ) / N) ^ n * ((A / c) ^ n * Y) := by
  have hC : 0 < C := hc.trans_le hcC
  have h1 : A * n ≤ A / c * (C * n) := by
    rw [show A / c * (C * n) = A * n * (C / c) by field_simp]
    exact le_mul_of_one_le_right (by positivity) ((one_le_div hc).2 hcC)
  calc Z ≤ (A * n) ^ n * Y := hZ
    _ ≤ (A / c * (C * n)) ^ n * Y :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h1 n) hY
    _ = (N * C) ^ n * ((n : ℝ) / N) ^ n * ((A / c) ^ n * Y) := by
        have e : N * C * ((n : ℝ) / N) = C * n := by field_simp
        rw [← mul_pow, e, mul_pow]
        ring

end BadPointTypes

end MultipoleBKT

end
