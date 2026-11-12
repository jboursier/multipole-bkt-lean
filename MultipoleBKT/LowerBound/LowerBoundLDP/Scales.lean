/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.TheoremTwo.Parameters

/-!
# Proposition 4.62: the truncation scale against the error rate

Facts on `R̄_{β,λ}^{-2}` (`truncationScale p₀ β λ ^ (-2)`) used implicitly in the proof of
Proposition 4.62 and in Lemma 4.59:

* `rpow_neg_two_truncationScale_le_errorRate`: `R̄_{β,λ}^{-2} ≤ δ_{β,λ}` for `λ ∈ (0, 1]`;
* `exists_rpow_neg_two_truncationScale_le`: for every `η > 0`, `R̄_{β,λ}^{-2} ≤ η λ^{2(p(β)-1)}`
  for `λ` small (for `β < 4`, `R̄^{-2} = λ^{2(β-2)/(4-β)}` and `2(β-2)/(4-β) > 2(p-1)` since
  `β > β_p`; for `β ≥ 4`, `R̄^{-2} = λ^{4p₀}`);
* `inv_sq_mul_truncationScale`: `((ε₀ R̄)²)⁻¹ = (ε₀²)⁻¹ R̄^{-2}`.
-/

@[expose] public section

namespace MultipoleBKT

namespace LowerBoundLDP

open TheoremTwo

theorem rpow_neg_two_truncationScale_of_lt {p₀ : ℕ} {β lam : ℝ} (h4 : β < 4) (hlam : 0 < lam) :
    truncationScale p₀ β lam ^ (-2 : ℝ) = lam ^ (2 * (β - 2) / (4 - β)) := by
  rw [Appendix.truncationScale_of_lt h4 hlam, ← Real.rpow_mul hlam.le]
  congr 1
  have : (4 - β) ≠ 0 := by linarith
  field_simp

theorem rpow_neg_two_truncationScale_of_ge {p₀ : ℕ} {β lam : ℝ} (h4 : 4 ≤ β) (hlam : 0 < lam) :
    truncationScale p₀ β lam ^ (-2 : ℝ) = lam ^ (4 * p₀) := by
  rw [Appendix.truncationScale_of_ge h4, ← Real.rpow_intCast, ← Real.rpow_mul hlam.le,
    ← Real.rpow_natCast]
  congr 1
  push_cast
  ring

/-- `R̄_{β,λ}^{-2} ≤ δ_{β,λ}` for `β > 2` and `λ ∈ (0, 1]`. -/
theorem rpow_neg_two_truncationScale_le_errorRate {p₀ : ℕ} {β lam : ℝ} (hβ : 2 < β)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    truncationScale p₀ β lam ^ (-2 : ℝ) ≤ errorRate p₀ β lam := by
  by_cases h4 : β < 4
  · rw [rpow_neg_two_truncationScale_of_lt h4 hlam, errorRate_of_lt_four' hβ h4 hlam]
    have h0 := tsum_transition_nonneg β lam
    have hpos : 0 ≤ lam ^ (2 * (β - 2) / (4 - β)) := Real.rpow_nonneg hlam.le _
    nlinarith
  · rw [rpow_neg_two_truncationScale_of_ge (not_lt.mp h4) hlam, errorRate_of_four_le (not_lt.mp h4)]
    exact pow_le_pow_of_le_one hlam.le hlam1 (by omega)

/-- **`R̄^{-2} = o(λ^{2(p-1)})`**: for `η > 0` there is `λ₀ ∈ (0, 1]` with
`R̄_{β,λ}^{-2} ≤ η λ^{2(p(β)-1)}` for `λ ∈ (0, λ₀)`. -/
theorem exists_rpow_neg_two_truncationScale_le {p₀ : ℕ} (hp₀ : 1 ≤ p₀) {β : ℝ} (hβ : 2 < β)
    {η : ℝ} (hη : 0 < η) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      truncationScale p₀ β lam ^ (-2 : ℝ) ≤ η * (lam ^ 2) ^ (pBeta p₀ β - 1) := by
  by_cases h4 : β < 4
  · set p := pBeta p₀ β
    have hp1 : 1 ≤ p := one_le_pBeta' hp₀ hβ
    have hlt := transitionBeta_pBeta_lt hp₀ hβ
    have h4' : 0 < 4 - β := by linarith
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
    have hkey : (4 - β) * p < 2 := by
      unfold transitionBeta at hlt
      have : 4 - β < 2 / (p : ℝ) := by linarith
      rwa [lt_div_iff₀ hp0] at this
    set θ : ℝ := 2 * (β - 2) / (4 - β) - 2 * ((p : ℝ) - 1)
    have hθ : 0 < θ := by
      have : 2 * (β - 2) / (4 - β) - 2 * ((p : ℝ) - 1) = 2 * (2 - (4 - β) * p) / (4 - β) := by
        field_simp
        ring
      simp only [θ]
      rw [this]
      have : 0 < 2 - (4 - β) * p := by linarith
      positivity
    refine ⟨min 1 (η ^ θ⁻¹), lt_min one_pos (Real.rpow_pos_of_pos hη _), min_le_left _ _,
      fun lam hlam hlt' => ?_⟩
    have hlamη : lam < η ^ θ⁻¹ := hlt'.trans_le (min_le_right _ _)
    rw [rpow_neg_two_truncationScale_of_lt h4 hlam]
    have hsplit : lam ^ (2 * (β - 2) / (4 - β)) = (lam ^ 2) ^ (p - 1) * lam ^ θ := by
      rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_add hlam]
      congr 1
      simp only [θ]
      push_cast [Nat.cast_sub hp1]
      ring
    rw [hsplit, mul_comm η]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 : lam ^ θ ≤ (η ^ θ⁻¹) ^ θ := Real.rpow_le_rpow hlam.le hlamη.le hθ.le
    rwa [← Real.rpow_mul hη.le, inv_mul_cancel₀ hθ.ne', Real.rpow_one] at h1
  · refine ⟨min 1 η, lt_min one_pos hη, min_le_left _ _, fun lam hlam hlt' => ?_⟩
    have hlam1 : lam ≤ 1 := (hlt'.trans_le (min_le_left _ _)).le
    have hlamη : lam ≤ η := (hlt'.trans_le (min_le_right _ _)).le
    rw [rpow_neg_two_truncationScale_of_ge (not_lt.mp h4) hlam]
    have hp : pBeta p₀ β = p₀ := by unfold pBeta; rw [ite_eq_right h4]
    rw [hp, ← pow_mul]
    have he : 4 * p₀ = 2 * (p₀ - 1) + (2 * p₀ + 2) := by omega
    rw [he, pow_add, mul_comm η]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc lam ^ (2 * p₀ + 2) ≤ lam ^ 1 := pow_le_pow_of_le_one hlam.le hlam1 (by omega)
      _ = lam := pow_one lam
      _ ≤ η := hlamη

/-- `((ε₀ R̄)²)⁻¹ = (ε₀²)⁻¹ R̄^{-2}`. -/
theorem inv_sq_mul_truncationScale {p₀ : ℕ} {β lam ε₀ : ℝ} (hlam : 0 < lam) :
    ((ε₀ * truncationScale p₀ β lam) ^ 2)⁻¹ =
      (ε₀ ^ 2)⁻¹ * truncationScale p₀ β lam ^ (-2 : ℝ) := by
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  rw [Real.rpow_neg hR.le, mul_pow, mul_inv]
  norm_cast

end LowerBoundLDP

end MultipoleBKT

end
