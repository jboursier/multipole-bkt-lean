/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeTwoCount.HighBlock

/-!
# Explicit enumeration with the sharp high-beta block bound

The paper: (5.140) and (5.141). Insert the sharp block estimate of Lemma 5.41 into the partition enumeration.
The coefficient uses `sourceEta`, with a logarithm only at beta four.
-/

@[expose] public section

namespace MultipoleBKT.BadPointTypes

open MeasureTheory Finset
open scoped ENNReal

/-- The written exponential summation using the sharp block coefficient of Lemma 5.41.
This retains Cayley's count before its final absorption into an exponential constant. -/
theorem typeTwoOnePartitionFunction_le_exp_high_source {χ : ℂ → ℝ} {β M : ℝ} {p₀ : ℕ}
    (hχ : IsMollifier χ) (hβ : 4 ≤ β) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ ≤ 1 →
      lam ≤ cutoff p₀ β lam ε₀ → ∀ N n : ℕ, ∀ y : ℝ, 0 < y →
      typeTwoOnePartitionFunction χ p₀ β lam M ε₀ N n ≤
        ENNReal.ofReal (n.factorial / y ^ n * Real.exp (∑ m ∈ range n,
          (if p₀ < m + 1 then
            (N : ℝ) * ((m + 1) ^ (m + 1 - 2) : ℕ) *
              (C ^ (m + 1) * lam ^ ((2 - β) * (m + 1)) * lam ^ (2 * p₀) *
                sourceEta β lam ^ (m + 1 - (p₀ + 1))) else 0) /
            (m + 1).factorial * y ^ (m + 1))) := by
  obtain ⟨C, hC, hb⟩ := lintegral_blockWeight_cut_le_high_source (p₀ := p₀) hχ hβ hM
  refine ⟨C, hC, fun lam hlam ε₀ hε₀ hε₀1 hlh N n y hy => ?_⟩
  let b : ℕ → ℝ := fun m => (N : ℝ) * (m ^ (m - 2) : ℕ) *
    (C ^ m * lam ^ ((2 - β) * m) * lam ^ (2 * p₀) * sourceEta β lam ^ (m - (p₀ + 1)))
  have hη : 0 ≤ sourceEta β lam := by unfold sourceEta; split_ifs <;> positivity
  have hb0 : ∀ m, 0 ≤ b m := fun m => by dsimp [b]; positivity
  have hp : pBeta p₀ β = p₀ := by unfold pBeta; rw [ite_eq_right (by linarith)]
  have hblock : ∀ T : Finset (Fin n), pBeta p₀ β < T.card →
      ∫⁻ c : T → ℂ × ℂ,
        blockWeight M lam (cutDipoleWeight χ β lam (cutoff p₀ β lam ε₀) N) c ≤
          ENNReal.ofReal (b T.card) := by
    intro T hT
    rw [hp] at hT
    have : Nonempty T := Fintype.card_pos_iff.1 (by simp only [Fintype.card_coe]; omega)
    have h := hb lam hlam ε₀ hε₀ hε₀1 hlh N T (by simp only [Fintype.card_coe]; omega)
    simp only [Fintype.card_coe] at h
    refine h.trans (le_of_eq ?_)
    dsimp [b]
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (N : ℝ) * (T.card ^ (T.card - 2) : ℕ)),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ N), ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast]
  have h := typeTwoOnePartitionFunction_le_exp hχ hlam p₀ ε₀ N b hb0 hblock hy
  simpa only [hp, b, Nat.cast_add, Nat.cast_one] using h

/-- The written leaf gain tends to zero. This elementary bound also covers
beta four, using `log(λ⁻¹) ≤ λ⁻¹ - 1` (the paper proof of Lemma 5.41). -/
theorem sourceEta_le_self {β lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    sourceEta β lam ≤ lam := by
  unfold sourceEta
  split_ifs with h4
  · rw [abs_of_nonpos (Real.log_nonpos hlam.le hlam1)]
    have hlog := Real.log_le_sub_one_of_pos (inv_pos.2 hlam)
    rw [Real.log_inv] at hlog
    calc
      lam ^ 2 * (1 + -Real.log lam) ≤ lam ^ 2 * lam⁻¹ := by gcongr; linarith
      _ = lam := by field_simp
  · simp only [add_zero, mul_one]
    nlinarith

/-- Dipole normalization and the factorial estimate give the written
`m f_β(m) C^m e^{tm}` coefficient (the paper proof of Lemma 5.41).
Cayley's exact count is kept until this scalar estimate. -/
theorem high_source_term_le {p₀ m N : ℕ} {β lam C c₀ t : ℝ}
    (hm : p₀ < m) (hlam : 0 < lam) (hC : 0 < C) (hc₀ : 0 < c₀) :
    ((N : ℝ) * (m ^ (m - 2) : ℕ) *
      (C ^ m * lam ^ ((2 - β) * m) * lam ^ (2 * p₀) *
        sourceEta β lam ^ (m - (p₀ + 1)))) / m.factorial *
      (Real.exp t / (c₀ * lam ^ (2 - β))) ^ m ≤
        N * ((m : ℝ) * lam ^ (2 * p₀) *
          (Real.exp 1 * C * Real.exp t / c₀) ^ m *
            sourceEta β lam ^ (m - (p₀ + 1))) := by
  have hm1 : 1 ≤ m := by omega
  have hη : 0 ≤ sourceEta β lam := by unfold sourceEta; split_ifs <;> positivity
  have hfac : ((m ^ (m - 2) : ℕ) : ℝ) / m.factorial ≤ Real.exp 1 ^ m := by
    calc
      _ ≤ ((m ^ m : ℕ) : ℝ) / m.factorial := by
        gcongr; omega
      _ ≤ _ := by
        have h := Real.pow_div_factorial_le_exp (m : ℝ) (Nat.cast_nonneg m) m
        rw [← Real.exp_nat_mul, mul_one]
        exact_mod_cast h
  have hlb : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  have hcancel : lam ^ ((2 - β) * m) *
      (Real.exp t / (c₀ * lam ^ (2 - β))) ^ m = (Real.exp t / c₀) ^ m := by
    rw [Real.rpow_mul_natCast hlam.le, ← mul_pow]
    congr 1
    field_simp
  have heq : ((N : ℝ) * (m ^ (m - 2) : ℕ) *
      (C ^ m * lam ^ ((2 - β) * m) * lam ^ (2 * p₀) *
        sourceEta β lam ^ (m - (p₀ + 1)))) / m.factorial *
      (Real.exp t / (c₀ * lam ^ (2 - β))) ^ m =
        (((m ^ (m - 2) : ℕ) : ℝ) / m.factorial) *
          (N * lam ^ (2 * p₀) * C ^ m * (Real.exp t / c₀) ^ m *
            sourceEta β lam ^ (m - (p₀ + 1))) := by
    calc
      _ = (((m ^ (m - 2) : ℕ) : ℝ) / m.factorial) *
          (N * lam ^ (2 * p₀) * C ^ m *
            (lam ^ ((2 - β) * m) * (Real.exp t / (c₀ * lam ^ (2 - β))) ^ m) *
              sourceEta β lam ^ (m - (p₀ + 1))) := by ring
      _ = _ := by rw [hcancel]
  rw [heq]
  calc
    _ ≤ Real.exp 1 ^ m *
        (N * lam ^ (2 * p₀) * C ^ m * (Real.exp t / c₀) ^ m *
          sourceEta β lam ^ (m - (p₀ + 1))) :=
      mul_le_mul_of_nonneg_right hfac (by positivity)
    _ = N * (lam ^ (2 * p₀) * (Real.exp 1 * C * Real.exp t / c₀) ^ m *
        sourceEta β lam ^ (m - (p₀ + 1))) := by simp only [mul_pow, div_pow]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      have hx : 0 ≤ lam ^ (2 * p₀) * (Real.exp 1 * C * Real.exp t / c₀) ^ m *
          sourceEta β lam ^ (m - (p₀ + 1)) := by positivity
      simpa only [one_mul, mul_assoc] using
        mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ m by exact_mod_cast hm1) hx

/-- The written high-beta size series is bounded when `C e^t η ≤ 1/2`
(the paper proof of Lemma 5.41). The factor `m` is summed explicitly. -/
theorem high_source_series_le {p₀ : ℕ} {β lam z : ℝ} (hz : 0 ≤ z)
    (hw : z * sourceEta β lam ≤ 1 / 2) (n : ℕ) :
    ∑ m ∈ range n, (if p₀ < m + 1 then
      ((m + 1 : ℕ) : ℝ) * lam ^ (2 * p₀) * z ^ (m + 1) *
        sourceEta β lam ^ (m + 1 - (p₀ + 1)) else 0) ≤
      lam ^ (2 * p₀) * z ^ (p₀ + 1) * 2 ^ p₀ * 4 := by
  have hη : 0 ≤ sourceEta β lam := by unfold sourceEta; split_ifs <;> positivity
  have hlamPow : 0 ≤ lam ^ (2 * p₀) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg lam) _
  have hs : HasSum (fun m : ℕ => ((m : ℝ) + 1) * (1 / 2 : ℝ) ^ m) 4 := by
    have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
    have h2 := hasSum_geometric_of_norm_lt_one (ξ := (1 / 2 : ℝ)) (by norm_num)
    convert h1.add h2 using 1
    · ext m
      ring
    · norm_num
  have hsum : ∑ m ∈ range n, ((m : ℝ) + 1) * (1 / 2 : ℝ) ^ m ≤ 4 :=
    (hs.summable.sum_le_tsum (range n) (fun m _ => by positivity)).trans hs.tsum_eq.le
  calc
    _ ≤ ∑ m ∈ range n,
        (lam ^ (2 * p₀) * z ^ (p₀ + 1) * 2 ^ p₀) *
          (((m : ℝ) + 1) * (1 / 2 : ℝ) ^ m) := by
      apply sum_le_sum
      intro m _
      split_ifs with hm
      · obtain ⟨j, rfl⟩ : ∃ j, m = p₀ + j := ⟨m - p₀, by omega⟩
        have he : 2 ^ p₀ * (1 / 2 : ℝ) ^ (p₀ + j) = (1 / 2 : ℝ) ^ j := by
          rw [pow_add, ← mul_assoc, ← mul_pow]
          norm_num
        have hj : p₀ + j + 1 - (p₀ + 1) = j := by omega
        rw [hj, show p₀ + j + 1 = (p₀ + 1) + j by omega, pow_add]
        calc
          _ = (lam ^ (2 * p₀) * z ^ (p₀ + 1)) *
              (((p₀ + 1 + j : ℕ) : ℝ) * (z * sourceEta β lam) ^ j) := by
            rw [mul_pow]; push_cast; ring
          _ ≤ (lam ^ (2 * p₀) * z ^ (p₀ + 1)) *
              (((p₀ + 1 + j : ℕ) : ℝ) * (1 / 2 : ℝ) ^ j) := by gcongr
          _ = _ := by rw [← he]; push_cast; ring
      · positivity
    _ = (lam ^ (2 * p₀) * z ^ (p₀ + 1) * 2 ^ p₀) *
        ∑ m ∈ range n, ((m : ℝ) + 1) * (1 / 2 : ℝ) ^ m := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

/-- The full infinite series in Lemma 5.41, the paper, converges and is `O(λ^(2p₀))`. -/
theorem high_source_series_summable_and_tsum_le {p₀ : ℕ} {β lam z : ℝ} (hz : 0 ≤ z)
    (hw : z * sourceEta β lam ≤ 1 / 2) :
    Summable (fun m : ℕ => if p₀ < m + 1 then
      ((m + 1 : ℕ) : ℝ) * lam ^ (2 * p₀) * z ^ (m + 1) *
        sourceEta β lam ^ (m + 1 - (p₀ + 1)) else 0) ∧
    (∑' m : ℕ, if p₀ < m + 1 then
      ((m + 1 : ℕ) : ℝ) * lam ^ (2 * p₀) * z ^ (m + 1) *
        sourceEta β lam ^ (m + 1 - (p₀ + 1)) else 0) ≤
      lam ^ (2 * p₀) * z ^ (p₀ + 1) * 2 ^ p₀ * 4 := by
  have hη : 0 ≤ sourceEta β lam := by unfold sourceEta; split_ifs <;> positivity
  have hlamPow : 0 ≤ lam ^ (2 * p₀) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg lam) _
  have hf : ∀ m : ℕ, 0 ≤ (if p₀ < m + 1 then
      ((m + 1 : ℕ) : ℝ) * lam ^ (2 * p₀) * z ^ (m + 1) *
        sourceEta β lam ^ (m + 1 - (p₀ + 1)) else 0) := by
    intro m
    split_ifs <;> positivity
  exact ⟨summable_of_sum_range_le hf (high_source_series_le hz hw),
    Real.tsum_le_of_sum_range_le hf (high_source_series_le hz hw)⟩

end MultipoleBKT.BadPointTypes

end
