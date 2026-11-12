/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeTwoIntegral.Core

/-!
# Scaling and finiteness of the ordered core

The paper: Lemma 5.41. Rescaling the ordered integral gives its power of lambda.
The unit-scale integral is finite also at beta four, so its coefficient
can be absorbed into the constant in the terminal-core estimate.
-/

@[expose] public section

namespace MultipoleBKT.BadPointTypes

open MeasureTheory Finset MultipoleIntegral Set
open scoped ENNReal Classical

variable {χ : ℂ → ℝ} {β lam : ℝ}

/-- Exact scaling of the literal core integral. -/
theorem orderedCoreBound_scale (hβ : 4 ≤ β) (hlam : 0 < lam) {k : ℕ} (hk : 1 ≤ k) :
    orderedCoreBound χ β lam k = ENNReal.ofReal (lam ^ ((4 - β) * k - 2)) *
      orderedCoreBound χ β 1 k := by
  have hE : (4 - β) * k - 2 < 0 := by
    have : (4 - β) * (k : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg k)
    linarith
  have hs := orderedRadial_eq_unit_coefficient (by linarith : 2 < β) hk hE hlam
  have hfin : orderedRadial β 1 (Ioi 0) (k - 1) ≠ ⊤ := by
    by_cases hk2 : 2 ≤ k
    · exact orderedRadial_infinite_ne_top (by linarith) hk2 hE (by norm_num)
    · have hk1 : k = 1 := by omega
      subst k
      exact orderedRadial_singleton_ne_top (by linarith) (by norm_num)
  rw [ENNReal.ofReal_toReal hfin] at hs
  unfold orderedCoreBound
  rw [hs]
  ring

/-- The ordered core is finite, including the logarithmic inner integral at beta four. -/
theorem orderedCoreBound_ne_top (hβ : 4 ≤ β) {k : ℕ} (hk : 1 ≤ k) :
    orderedCoreBound χ β 1 k ≠ ⊤ := by
  unfold orderedCoreBound
  apply ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  apply ENNReal.mul_ne_top
  · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top k) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  · by_cases hk2 : 2 ≤ k
    · apply orderedRadial_infinite_ne_top (by linarith) hk2 _ (by norm_num)
      have : (4 - β) * (k : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg k)
      linarith
    · have hk1 : k = 1 := by omega
      subst k
      exact orderedRadial_singleton_ne_top (by linarith) (by norm_num)

/-- A scalar coefficient for the convergent ordered core. -/
theorem orderedCoreBound_le_power (hβ : 4 ≤ β) {k : ℕ} (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam →
      orderedCoreBound χ β lam k ≤ ENNReal.ofReal (C * lam ^ ((4 - β) * k - 2)) := by
  let C := (orderedCoreBound χ β 1 k).toReal + 1
  refine ⟨C, by dsimp [C]; positivity, fun lam hlam => ?_⟩
  rw [orderedCoreBound_scale hβ hlam hk, ENNReal.ofReal_mul (by positivity)]
  rw [mul_comm (ENNReal.ofReal C)]
  apply mul_le_mul' le_rfl
  have : 0 ≤ (orderedCoreBound χ β 1 k).toReal := ENNReal.toReal_nonneg
  exact (show orderedCoreBound χ β 1 k ≤ ENNReal.ofReal C from by
    rw [← ENNReal.ofReal_toReal (orderedCoreBound_ne_top hβ hk)]
    exact ENNReal.ofReal_le_ofReal (by dsimp [C]; linarith))

end MultipoleBKT.BadPointTypes

end
