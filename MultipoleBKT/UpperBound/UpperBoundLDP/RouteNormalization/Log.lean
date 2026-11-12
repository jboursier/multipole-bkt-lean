/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Hierarchical.DipoleMeasure
public import MultipoleBKT.LowerBound.LowerBoundLDP.Bounds
public import MultipoleBKT.LowerBound.LowerBoundLDP.Scales

/-!
# The logarithmic normalization in Proposition 5.43

The paper: Proposition 5.43, using (4.11) in Lemma 4.12.
The two-sided estimate for the cutoff normalizer gives the displayed expansion
of `N log C`. Both logarithmic bounds follow from that estimate. The upper
bound retains its quantitative error for the final absorption into `N δ`.
-/

@[expose] public section

open MeasureTheory Filter Metric
open scoped Topology

namespace MultipoleBKT.UpperBoundLDP.RouteNormalization

open Hierarchical

/-- Internal quantitative logarithm step for the (4.11) expansion at the end of
Proposition 5.43. The coefficient is
chosen before `p₀, ε₀, λ`. The relative-error condition makes taking logarithms
quantitative. Neither logarithmic bound uses a sign of the correction. -/
theorem eventually_log_normalization_of_small_error {χ : ℂ → ℝ} (hχ : IsMollifier χ)
    {β : ℝ} (hβ : 2 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p₀ : ℕ) (ε₀ lam : ℝ),
      0 < ε₀ → ε₀ < 1 → 0 < lam → lam < 1 →
      C * ((ε₀ * truncationScale p₀ β lam) ^ 2)⁻¹ ≤ dipoleConstant χ β / 2 →
      ∀ᶠ N : ℕ in atTop,
        |(N : ℝ) * Real.log (cutoffDipoleNormalization χ N p₀ β lam ε₀) -
            (N * (2 - β) * Real.log lam + N * Real.log (dipoleConstant χ β))| ≤
          (2 * C / dipoleConstant χ β) * N *
            ((ε₀ * truncationScale p₀ β lam) ^ 2)⁻¹ := by
  obtain ⟨C, hC, hdevt⟩ := lem411_devtCbeta_eventually hχ hβ
  refine ⟨C, hC, fun p₀ ε₀ lam hε₀ hε₁ hlam hlam1 hsmall => ?_⟩
  have hZ : 0 < dipoleConstant χ β := dipoleConstant_pos hχ hβ
  filter_upwards [hdevt p₀ ε₀ lam hε₀ hε₁ hlam hlam1] with N hdevtN
  obtain ⟨hpos, hlow⟩ := LowerBoundLDP.log_ge_of_abs_sub_le hlam hZ
    (by positivity) hsmall hdevtN
  let η := C * ((ε₀ * truncationScale p₀ β lam) ^ 2)⁻¹
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hupp : cutoffDipoleNormalization χ N p₀ β lam ε₀ ≤
      lam ^ (2 - β) * (dipoleConstant χ β + η) := by
    have := (abs_le.mp hdevtN).2
    dsimp [η]
    nlinarith
  have hlog := Real.log_le_log hpos hupp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hlam] at hlog
  have hratio := Real.log_le_sub_one_of_pos
    (div_pos (add_pos_of_pos_of_nonneg hZ hη) hZ)
  rw [Real.log_div (by positivity) hZ.ne'] at hratio
  have hquot : (dipoleConstant χ β + η) / dipoleConstant χ β - 1 =
      η / dipoleConstant χ β := by field_simp; ring
  rw [hquot] at hratio
  have hlogUpper : Real.log (cutoffDipoleNormalization χ N p₀ β lam ε₀) ≤
      (2 - β) * Real.log lam + Real.log (dipoleConstant χ β) +
        2 * η / dipoleConstant χ β := by
    have : 0 ≤ η / dipoleConstant χ β := div_nonneg hη hZ.le
    rw [mul_div_assoc]
    linarith
  have hloN := mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg N)
  have hupN := mul_le_mul_of_nonneg_left hlogUpper (Nat.cast_nonneg N)
  dsimp [η] at hupN
  rw [abs_le]
  simp only [div_eq_mul_inv] at hloN hupN ⊢
  constructor <;> nlinarith [hloN, hupN]

/-- The displayed two-sided expansion `N log C = N log (λ^(2-β) 𝒵) + O(N R̄⁻²)`
in Proposition 5.43. The coefficient
depends on `χ, β, ε₀`, and the threshold can also depend on `p₀`. -/
theorem log_normalization_expansion {χ : ℂ → ℝ} (hχ : IsMollifier χ)
    {β : ℝ} (hβ : 2 < β) (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₁ : ε₀ < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ p₀ : ℕ, 1 ≤ p₀ → ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∀ᶠ N : ℕ in atTop,
        |(N : ℝ) * Real.log (cutoffDipoleNormalization χ N p₀ β lam ε₀) -
            (N * (2 - β) * Real.log lam + N * Real.log (dipoleConstant χ β))| ≤
          K * N * truncationScale p₀ β lam ^ (-2 : ℝ) := by
  obtain ⟨C, hC, hlog⟩ := eventually_log_normalization_of_small_error hχ hβ
  have hZ := dipoleConstant_pos hχ hβ
  refine ⟨(2 * C / dipoleConstant χ β) * (ε₀ ^ 2)⁻¹, by positivity, fun p₀ hp₀ => ?_⟩
  let η := dipoleConstant χ β / (2 * (C * (ε₀ ^ 2)⁻¹))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨lam₀, hlam₀, hlam₁, hR⟩ :=
    LowerBoundLDP.exists_rpow_neg_two_truncationScale_le hp₀ hβ hη
  refine ⟨lam₀, hlam₀, fun lam hlam hlt => ?_⟩
  have hlam1 : lam < 1 := hlt.trans_le hlam₁
  have hscale : truncationScale p₀ β lam ^ (-2 : ℝ) ≤ η :=
    (hR lam hlam hlt).trans (mul_le_of_le_one_right hη.le
      (pow_le_one₀ (sq_nonneg lam) (by nlinarith [hlam1.le])))
  have hsmall : C * ((ε₀ * truncationScale p₀ β lam) ^ 2)⁻¹ ≤ dipoleConstant χ β / 2 := by
    rw [LowerBoundLDP.inv_sq_mul_truncationScale hlam, ← mul_assoc]
    calc C * (ε₀ ^ 2)⁻¹ * truncationScale p₀ β lam ^ (-2 : ℝ)
        ≤ C * (ε₀ ^ 2)⁻¹ * η := mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = dipoleConstant χ β / 2 := by dsimp [η]; field_simp
  filter_upwards [hlog p₀ ε₀ lam hε₀ hε₁ hlam hlam1 hsmall] with N hN
  calc _ ≤ (2 * C / dipoleConstant χ β) * N *
        ((ε₀ * truncationScale p₀ β lam) ^ 2)⁻¹ := hN
    _ = _ := by rw [LowerBoundLDP.inv_sq_mul_truncationScale hlam]; ring

end MultipoleBKT.UpperBoundLDP.RouteNormalization

end
