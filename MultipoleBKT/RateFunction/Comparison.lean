/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.RateFunction.Minimizer

/-!
# Comparison of the infima of the rate function over `Δ_{p,x}` and `Δ_{p,0}`

Equation (5.153) of the proof of Theorem 2: for `x ∈ [0,1]`,

  `inf_{Δ_{p,x}} ℐ ≥ inf_{Δ_{p,0}} ℐ - C' x λ²`

(`MultipoleBKT.rateFunction_inf_comparison`). For `γ ∈ Δ_{p,x}`, the point
`η = (γ₁ + x, γ₂, …, γ_p)` lies in `Δ_{p,0}`; since `𝗆(1) = 1`, the first entropy term is
`s ↦ s(log s - 1)`, which is nonincreasing on `[0,1]`, and `h` is `C'λ²`-Lipschitz, so
`ℐ(η) ≤ ℐ(γ) + C' x λ²`. Infima are `sInf` of images, as in the frozen Theorem 2.
-/

@[expose] public section

namespace MultipoleBKT

open Finset Real Set

variable {p : ℕ}

/-- `s ↦ s (log s - 1)` is nonincreasing on `[0,1]`. -/
theorem mul_log_sub_one_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    b * (Real.log b - 1) ≤ a * (Real.log a - 1) := by
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_mul]
    have hb0 : 0 ≤ b := hab
    have : Real.log b ≤ 0 := Real.log_nonpos hb0 hb
    exact mul_nonpos_of_nonneg_of_nonpos hb0 (by linarith)
  · have hb0 : 0 < b := ha'.trans_le hab
    have h1 : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hb0.ne' ha'.ne'] at h1
    have h2 : a * (Real.log b - Real.log a) ≤ b - a := by
      have := mul_le_mul_of_nonneg_left h1 ha'.le
      calc a * (Real.log b - Real.log a) ≤ a * (b / a - 1) := this
        _ = b - a := by field_simp
    have h3 : (b - a) * Real.log b ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (Real.log_nonpos hb0.le hb)
    nlinarith

/-- Points of `Δ_{p,x}` lie in the region `|γᵢ| ≤ 2` of
`MultipoleBKT.rateSeries_summable_and_bound`. -/
theorem abs_le_two_of_mem_simplex {x : ℝ} {γ : Fin p → ℝ} (hγ : γ ∈ simplex p x) (i : Fin p) :
    |γ i| ≤ 2 := by
  rw [abs_le]
  constructor <;> linarith [(hγ.1 i).1, (hγ.1 i).2]

variable {msf : ℕ → ℝ} {kmult : (ℕ →₀ ℕ) → ℝ} {C lam : ℝ}

/-- The comparison of infima at a fixed small `λ`, with `B = 16 K² 2^p λ²`. -/
theorem sInf_rateFunction_comparison (hp : 1 ≤ p) (hk : KmultBound p kmult C lam)
    (hlam : 0 ≤ lam) (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) (hmsf1 : msf 1 = 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    sInf (rateFunction p msf kmult '' simplex p 0) -
        16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 * x ≤
      sInf (rateFunction p msf kmult '' simplex p x) := by
  set B := 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2
  have hB0 : 0 ≤ B := by positivity
  have hcont := continuousOn_rateFunction (msf := msf) hk hlam hsmall
  have hbdd : BddBelow (rateFunction p msf kmult '' simplex p 0) :=
    (isCompact_simplex 0).bddBelow_image
      (hcont.mono ((simplex_subset_unitBox 0).trans unitBox_subset_rateDomain))
  refine le_csInf ((simplex_nonempty hp hx).image _) ?_
  rintro _ ⟨γ, hγ, rfl⟩
  set e0 : Fin p := ⟨0, hp⟩
  set w : Fin p → ℝ := Pi.single e0 1 with hw_def
  have hwe : w e0 = 1 := by simp [hw_def]
  have hwk : ∀ k, k ≠ e0 → w k = 0 := fun k hk => by simp [hw_def, hk]
  set η : Fin p → ℝ := γ + x • w with hη_def
  have hηk : ∀ k, η k = γ k + x * w k := fun k => by simp [hη_def]
  have hγ0 : γ e0 + x ≤ 1 := by
    have h1 : ∑ k ∈ ({e0} : Finset (Fin p)), ((k : ℕ) + 1 : ℝ) * γ k ≤
        ∑ k : Fin p, ((k : ℕ) + 1 : ℝ) * γ k :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) fun k _ _ =>
        mul_nonneg (by positivity) (hγ.1 k).1
    rw [sum_singleton, hγ.2] at h1
    simp only [e0, Nat.cast_zero, zero_add, one_mul] at h1
    linarith
  have hηmem : η ∈ simplex p 0 := by
    refine ⟨fun k => ?_, ?_⟩
    · rw [hηk]
      by_cases hk : k = e0
      · rw [hk, hwe, mul_one]
        exact ⟨by linarith [(hγ.1 e0).1, hx.1], hγ0⟩
      · rw [hwk k hk, mul_zero, add_zero]
        exact hγ.1 k
    · have : ∑ k : Fin p, ((k : ℕ) + 1 : ℝ) * η k =
          ∑ k : Fin p, ((k : ℕ) + 1 : ℝ) * γ k + x * ∑ k : Fin p, ((k : ℕ) + 1 : ℝ) * w k := by
        rw [mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun k _ => ?_
        rw [hηk]
        ring
      have hw : ∑ k : Fin p, ((k : ℕ) + 1 : ℝ) * w k = 1 := by
        rw [Fintype.sum_eq_single e0 fun k hk => by rw [hwk k hk, mul_zero], hwe]
        simp [e0]
      rw [this, hγ.2, hw]
      ring
  have h1 : sInf (rateFunction p msf kmult '' simplex p 0) ≤ rateFunction p msf kmult η :=
    csInf_le hbdd ⟨η, hηmem, rfl⟩
  have h2 : rateFunction p msf kmult η - rateFunction p msf kmult γ ≤ B * x := by
    rw [rateFunction_sub_eq]
    have hsum : ∑ k, (rateEntTerm msf k (η k) - rateEntTerm msf k (γ k)) =
        rateEntTerm msf e0 (η e0) - rateEntTerm msf e0 (γ e0) := by
      refine Fintype.sum_eq_single e0 fun k hk => ?_
      rw [hηk, hwk k hk, mul_zero, add_zero, sub_self]
    have hent : rateEntTerm msf e0 (η e0) - rateEntTerm msf e0 (γ e0) ≤ 0 := by
      rw [hηk, hwe, mul_one]
      have hform : ∀ s : ℝ, rateEntTerm msf e0 s = s * (Real.log s - 1) := by
        intro s
        simp only [rateEntTerm, e0, zero_add, Nat.factorial_one, Nat.cast_one,
          Real.log_one, hmsf1]
        ring
      rw [hform, hform]
      have := mul_log_sub_one_le (hγ.1 e0).1 (by linarith [hx.1] : γ e0 ≤ γ e0 + x) hγ0
      linarith
    have hH : rateCluster p kmult η - rateCluster p kmult γ ≤ B * x := by
      have hγD := unitBox_subset_rateDomain (simplex_subset_unitBox x hγ)
      have hηD := unitBox_subset_rateDomain (simplex_subset_unitBox 0 hηmem)
      have h := abs_rateCluster_sub_le hk hlam hsmall hγD hηD
      have hn : ‖η - γ‖ ≤ x := by
        rw [hη_def, add_sub_cancel_left]
        refine (pi_norm_le_iff_of_nonneg hx.1).mpr fun k => ?_
        simp only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hx.1]
        by_cases hk : k = e0
        · rw [hk, hwe, abs_one, mul_one]
        · rw [hwk k hk, abs_zero, mul_zero]
          exact hx.1
      calc rateCluster p kmult η - rateCluster p kmult γ ≤ B * ‖η - γ‖ :=
            (le_abs_self _).trans h
        _ ≤ B * x := mul_le_mul_of_nonneg_left hn hB0
    rw [hsum]
    linarith
  linarith

/-- **Comparison of infima** (equation (5.153)). For `p ≥ 1`
and every `C` there are `λ₀ > 0` and `C' > 0` such that for `0 < λ < λ₀`, coefficients
`kmult` satisfying (2.48) with constant `C`, `𝗆(1) = 1`, and `x ∈ [0,1]`,
`inf_{Δ_{p,x}} ℐ ≥ inf_{Δ_{p,0}} ℐ - C' x λ²`. -/
theorem rateFunction_inf_comparison (p : ℕ) (hp : 1 ≤ p) (C : ℝ) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∃ C' : ℝ, 0 < C' ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∀ (msf : ℕ → ℝ) (kmult : (ℕ →₀ ℕ) → ℝ), msf 1 = 1 → KmultBound p kmult C lam →
        ∀ x ∈ Icc (0 : ℝ) 1,
          sInf (rateFunction p msf kmult '' simplex p 0) - C' * x * lam ^ 2 ≤
            sInf (rateFunction p msf kmult '' simplex p x) := by
  refine ⟨rateSeriesLam₀ p C, rateSeriesLam₀_pos p C,
    16 * rateSeriesConst p C ^ 2 * 2 ^ p + 1, by positivity, ?_⟩
  intro lam hlam hlam₀ msf kmult hmsf1 hk x hx
  have hsmall := rateSeriesConst_mul_sq_le p C hlam.le hlam₀
  have h := sInf_rateFunction_comparison hp hk hlam.le hsmall hmsf1 hx
  have : 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 * x ≤
      (16 * rateSeriesConst p C ^ 2 * 2 ^ p + 1) * x * lam ^ 2 := by
    have : 0 ≤ x * lam ^ 2 := mul_nonneg hx.1 (sq_nonneg _)
    nlinarith
  linarith

end MultipoleBKT

end
