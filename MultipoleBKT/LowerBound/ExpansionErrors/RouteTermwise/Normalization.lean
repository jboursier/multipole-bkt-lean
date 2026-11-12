/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.ExpansionErrors.Blocks

/-!
# Reciprocal products and fixed expectation errors

The proofs of Propositions 4.24 and 5.19.
The numerator and the reciprocal-product error are multiplied for each
fixed datum before taking a sum over expansion data.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionErrors

/-- Internal reciprocal-product arithmetic after telescoping the blocks.
The positive factor `ℓ` retains the radius power until multiplication
by the fixed numerator bound. -/
theorem internal_reciprocal_error {Q₁ Q₀ ℓ η E : ℝ}
    (hQ₁ : 0 < Q₁) (hQ₀ : 0 < Q₀)
    (hd : |Q₀ - Q₁| * ℓ ≤ E * η * Q₁) :
    |Q₁⁻¹ - Q₀⁻¹| * ℓ ≤ E * η / Q₀ := by
  rw [inv_sub_inv hQ₁.ne' hQ₀.ne', abs_div, abs_of_pos (mul_pos hQ₁ hQ₀),
    div_mul_eq_mul_div, div_le_div_iff₀ (mul_pos hQ₁ hQ₀) hQ₀]
  exact mul_le_mul_of_nonneg_right hd hQ₀.le |>.trans_eq (by ring)

/-- Multiply (4.80) by the reciprocal error while retaining both powers.
proof of Proposition 4.24.
For `r = λ^{2(k-1)}` and `ℓ = λ^{2(max |S|-1)}`, the quotient `r / ℓ`
is exactly the two radius factors in the paper's penultimate bound. -/
theorem internal_fixed_normalization_error_sharp {I₀ Q₁ Q₀ P T r ℓ η E A : ℝ}
    (hQ₁ : 0 < Q₁) (hQ₀ : 0 < Q₀) (hPT : 0 < P * T) (hℓ : 0 < ℓ)
    (hA : 0 ≤ A) (hr : 0 ≤ r)
    (hnum : |I₀| * (P * T) ≤ A * r * Q₀)
    (hd : |Q₀ - Q₁| * ℓ ≤ E * η * Q₁) :
    |I₀| * |Q₁⁻¹ - Q₀⁻¹| ≤ A * E * η * (r / ℓ) / (P * T) := by
  rw [le_div_iff₀ hPT]
  have hrec := internal_reciprocal_error hQ₁ hQ₀ hd
  have hscaled : (|I₀| * |Q₁⁻¹ - Q₀⁻¹| * (P * T)) * ℓ ≤
      (A * E * η * (r / ℓ)) * ℓ := by
    calc _ = (|I₀| * (P * T)) * (|Q₁⁻¹ - Q₀⁻¹| * ℓ) := by ring
      _ ≤ (A * r * Q₀) * (E * η / Q₀) :=
        mul_le_mul hnum hrec (by positivity) (by positivity)
      _ = (A * E * η * (r / ℓ)) * ℓ := by field_simp
  exact le_of_mul_le_mul_right hscaled hℓ

/-- Absorb the remaining power only after multiplying (4.80) by the
reciprocal error. See the proof of Proposition 4.24. -/
theorem internal_fixed_normalization_error {I₀ Q₁ Q₀ P T r ℓ η E A : ℝ}
    (hQ₁ : 0 < Q₁) (hQ₀ : 0 < Q₀) (hPT : 0 < P * T) (hℓ : 0 < ℓ)
    (hA : 0 ≤ A) (hr : 0 ≤ r) (hrℓ : r ≤ ℓ)
    (hnum : |I₀| * (P * T) ≤ A * r * Q₀)
    (hd : |Q₀ - Q₁| * ℓ ≤ E * η * Q₁) :
    |I₀| * |Q₁⁻¹ - Q₀⁻¹| ≤ A * E * η / (P * T) := by
  have hEη : 0 ≤ E * η := by
    have hd0 := (mul_nonneg (abs_nonneg (Q₀ - Q₁)) hℓ.le).trans hd
    exact (mul_nonneg_iff_of_pos_right hQ₁).mp hd0
  have hratio : r / ℓ ≤ 1 := (div_le_one hℓ).2 hrℓ
  calc _ ≤ A * E * η * (r / ℓ) / (P * T) :=
      internal_fixed_normalization_error_sharp hQ₁ hQ₀ hPT hℓ hA hr hnum hd
    _ ≤ A * E * η / (P * T) := by
      apply div_le_div_of_nonneg_right _ hPT.le
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio
        (show 0 ≤ A * E * η by nlinarith [mul_nonneg hA hEη])

/-- Internal fixed-term form of (4.78): first bound the numerator
error and the normalization error separately, then add their bounds. -/
theorem internal_fixed_expectation_error {K₁ K₀ I₁ I₀ Q₁ Q₀ P T A B η : ℝ}
    (hQ₁ : 0 < Q₁) (hQ₀ : 0 < Q₀)
    (h₁ : Q₁ * K₁ = I₁) (h₀ : Q₀ * K₀ = I₀)
    (hn : |I₁ - I₀| / Q₁ ≤ A * η / (P * T))
    (hr : |I₀| * |Q₁⁻¹ - Q₀⁻¹| ≤ B * η / (P * T)) :
    |K₁ - K₀| ≤ (A + B) * η / (P * T) := by
  have hs : K₁ - K₀ = (I₁ - I₀) / Q₁ + I₀ * (Q₁⁻¹ - Q₀⁻¹) := by
    rw [← h₁, ← h₀]
    field_simp [hQ₁.ne', hQ₀.ne']
    ring
  calc |K₁ - K₀| ≤ |I₁ - I₀| / Q₁ + |I₀| * |Q₁⁻¹ - Q₀⁻¹| := by
        rw [hs]
        simpa only [abs_div, abs_of_pos hQ₁, abs_mul] using abs_add_le ((I₁ - I₀) / Q₁)
          (I₀ * (Q₁⁻¹ - Q₀⁻¹))
    _ ≤ A * η / (P * T) + B * η / (P * T) := add_le_add hn hr
    _ = _ := by ring

end MultipoleBKT.ExpansionErrors

end
