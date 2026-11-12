/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansion.CutoffTail
public import MultipoleBKT.Appendix.GeneralExpansion.RouteLog.CutWeight

/-!
# Final normalization of the cutoff cap

See (A.44).
After the logarithmic moments have been integrated, `cut_power_le` converts
the cap factor into `N λ^((2-β)k) R̄^(-2)`. The compatibility exponent is
introduced only in this final comparison.
-/

@[expose] public section

namespace MultipoleBKT

namespace GeneralExpansion

open MeasureTheory Set Finset Metric
open scoped ENNReal
open TwoComponentCoulomb (box)
open MultipoleIntegral

variable {χ : ℂ → ℝ} {β lam : ℝ}

/-- **The algebra of the term `CN/h²`**: with `σ = tailSigma p₀ β k` and `h = ε₀ R̄`,
`λ^{(4-β-σ)k} h^{σk-2} ≤ ε₀^{σk-2} λ^{(2-β)k} R̄^{-2}` for `0 < λ ≤ 1`. -/
theorem cut_power_le {p₀ : ℕ} {ε₀ : ℝ} {k : ℕ} (hk : 1 ≤ k) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hε₀ : 0 < ε₀) :
    lam ^ ((4 - β - tailSigma p₀ β k) * k) *
        (ε₀ * truncationScale p₀ β lam) ^ (tailSigma p₀ β k * k - 2) ≤
      ε₀ ^ (tailSigma p₀ β k * k - 2) *
        (lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ)) := by
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  set x := tailSigma p₀ β k * k - 2
  rw [Real.mul_rpow hε₀.le hR.le]
  have key : lam ^ ((4 - β - tailSigma p₀ β k) * k) * truncationScale p₀ β lam ^ x ≤
      lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ) := by
    by_cases hβ4 : β < 4
    · have hσ : tailSigma p₀ β k = 4 - β := by unfold tailSigma; rw [ite_eq_left hβ4]
      have hx : x = (4 - β) * k + (-2) := by simp only [x, hσ]; ring
      rw [hσ, hx, Real.rpow_add hR, Appendix.rpow_truncationScale_mul_of_lt hlam hβ4]
      rw [show (4 - β - (4 - β)) * (k : ℝ) = 0 by ring, Real.rpow_zero, one_mul]
    · push Not at hβ4
      have hRe : ∀ y : ℝ, truncationScale p₀ β lam ^ y = lam ^ (-(2 * (p₀ : ℝ)) * y) := by
        intro y
        rw [Appendix.truncationScale_of_ge hβ4, ← Real.rpow_intCast, ← Real.rpow_mul hlam.le]
        congr 1
        push_cast
        ring
      rw [hRe, hRe, ← Real.rpow_add hlam, ← Real.rpow_add hlam]
      refine Real.rpow_le_rpow_of_exponent_ge hlam hlam1 ?_
      have hσ : tailSigma p₀ β k = 1 / (k * (2 * p₀ + 1)) := by
        unfold tailSigma; rw [ite_eq_right (not_lt.2 hβ4)]
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hp : (0 : ℝ) ≤ p₀ := Nat.cast_nonneg p₀
      have hkey : tailSigma p₀ β k * k * (2 * p₀ + 1) = 1 := by
        rw [hσ]
        field_simp
      simp only [x]
      nlinarith
  calc lam ^ ((4 - β - tailSigma p₀ β k) * k) * (ε₀ ^ x * truncationScale p₀ β lam ^ x)
      = ε₀ ^ x * (lam ^ ((4 - β - tailSigma p₀ β k) * k) * truncationScale p₀ β lam ^ x) := by
        ring
    _ ≤ ε₀ ^ x * (lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left key (Real.rpow_nonneg hε₀.le _)

end GeneralExpansion

end MultipoleBKT

end
