/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.Scaling

/-!
# The finite-cutoff gamma normalization

See (A.2) and
(A.14). Below four, identify the remaining
power integral with Lemma A.2. At and above four, use the uniform ordered
bound and the negative-exponent branch of gamma.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegral

open MeasureTheory Set
open scoped ENNReal

/-- The core plus annular power integral in the low-temperature ordered
bound is exactly the radial integral of (A.2). -/
theorem ordered_power_eq_radialIntegral (p₀ : ℕ) {β lam eps : ℝ} {k : ℕ}
    (hlam : 0 < lam) (hlh : lam ≤ eps * truncationScale p₀ β lam) :
    lam ^ ((4 - β) * k - 2) +
      (∫ r in lam..(eps * truncationScale p₀ β lam), r ^ ((4 - β) * k - 3)) =
        Appendix.radialIntegral p₀ β lam k eps := by
  rw [Appendix.radialIntegral_eq, Appendix.integral_indicator_Iic,
    Appendix.integral_Ioc_max_rpow hlam hlh]
  congr 1 <;> congr 1 <;> ring_nf

/-- The finite-cutoff ordered integral, with the gamma factor of
Definition 4.22. No integrability restriction on the size is imposed. -/
theorem orderedRadial_gamma (p₀ : ℕ) {β : ℝ} (hβ : 2 < β) {k : ℕ} (hk : 2 ≤ k)
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ < 1 ∧
      ∀ lam : ℝ, 0 < lam → lam ≤ lam₀ →
        orderedRadial β lam (Ioc 0 (eps * truncationScale p₀ β lam)) (k - 1) ≤
          ENNReal.ofReal (C * (lam ^ ((2 - β) * k) * Appendix.gammaBeta p₀ β lam k)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hcard : j + 2 - 1 = j + 1 := by omega
  rw [hcard]
  have hcast : ((j + 2 : ℕ) : ℝ) = (j : ℝ) + 2 := by push_cast; rfl
  by_cases hb4 : β < 4
  · obtain ⟨A, hA, hbound⟩ := orderedRadial_lt_four hβ hb4 j
    let B := Appendix.radialConst β (j + 2) eps
    have hB : 0 < B := Appendix.radialConst_pos (by omega) heps
    refine ⟨A * B, mul_pos hA hB, Appendix.lamBound eps (j + 2),
      Appendix.lamBound_pos heps _, Appendix.lamBound_lt_one _ _, fun lam hlam hle => ?_⟩
    have hrad := Appendix.lemsupplapp_two_sided p₀ hβ (by omega : 1 ≤ j + 2)
      heps heps1 lam hlam hle
    have hlh : lam ≤ eps * truncationScale p₀ β lam := by
      obtain ⟨hhalf, he, _⟩ := Appendix.le_of_le_lamBound hle
      exact he.trans (le_mul_of_one_le_right heps.le
        (Appendix.one_le_truncationScale hβ hlam (by linarith)))
    have hp := hbound lam (eps * truncationScale p₀ β lam) hlam hlh
    rw [← hcast, ordered_power_eq_radialIntegral p₀ hlam hlh] at hp
    refine hp.trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      _ ≤ A * (B * (lam ^ ((2 - β) * (j + 2 : ℕ)) *
          Appendix.gammaBeta p₀ β lam (j + 2))) :=
        mul_le_mul_of_nonneg_left hrad.2.2 hA.le
      _ = _ := by ring
  · obtain ⟨A, hA, hbound⟩ := orderedRadial_infinite_ge_four (le_of_not_gt hb4) j
    refine ⟨A, hA, 1 / 2, by norm_num, by norm_num, fun lam hlam _ => ?_⟩
    have hE : (4 - β) * (j + 2 : ℕ) - 2 < 0 := by
      have : (4 - β) ≤ 0 := by linarith
      have : 0 ≤ (j + 2 : ℕ) := Nat.zero_le _
      have := mul_nonpos_of_nonpos_of_nonneg (show 4 - β ≤ 0 by linarith)
        (Nat.cast_nonneg (α := ℝ) (j + 2))
      linarith
    refine (lintegral_mono_set Ioc_subset_Ioi_self).trans ((hbound lam hlam).trans (le_of_eq ?_))
    rw [Appendix.target_neg hlam (by omega : 1 ≤ j + 2) hE, hcast]

end MultipoleBKT.MultipoleIntegral

end
