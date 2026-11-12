/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansion.FrozenRoot
public import MultipoleBKT.Appendix.SmallIntegral.TreeTerm

/-!
# The external gain of one dipole

See (A.18) and
(A.20). The distance is the minimum of
the cap and the four translated bad endpoints. The logarithmic integral
is in `RouteJext/Root.lean`.
-/

@[expose] public section

namespace MultipoleBKT

namespace SmallIntegral

open MeasureTheory Set Finset Metric
open scoped ENNReal
open TwoComponentCoulomb (box)
open Limits MultipoleIntegral UpperBound GeneralExpansion

variable {χ : ℂ → ℝ} {β lam : ℝ}

/-! ### The gain of one dipole and the root integral -/

section Root

variable {N p₀ : ℕ} {ε₀ : ℝ} {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}

/-- **The gain of one dipole** `min(1, R²/d_{e,bad}²)` (the factor of `J_ext`, eq. (A.18),
for one dipole). -/
noncomputable def gainW (p₀ : ℕ) (β lam ε₀ : ℝ) {N : ℕ} (V : Finset (Fin N))
    (Z : Fin N → ℂ × ℂ) (R : ℝ) (e : ℂ × ℂ) : ℝ :=
  min 1 (R ^ 2 / badDistZ p₀ β lam ε₀ V Z e ^ 2)

theorem gainW_nonneg (R : ℝ) (e : ℂ × ℂ) : 0 ≤ gainW p₀ β lam ε₀ V Z R e :=
  le_min zero_le_one (div_nonneg (sq_nonneg _) (sq_nonneg _))

theorem continuous_badDistZ' (p₀ : ℕ) (β lam ε₀ : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) :
    Continuous (badDistZ p₀ β lam ε₀ V Z) := by
  unfold badDistZ
  induction V using Finset.induction_on with
  | empty => simp only [Finset.fold_empty]; exact continuous_const
  | insert j V hj ih =>
    simp only [Finset.fold_insert hj]
    refine Continuous.min ?_ ih
    unfold dipoleDist
    fun_prop

theorem measurable_gainW (R : ℝ) : Measurable (gainW p₀ β lam ε₀ V Z R) := by
  unfold gainW
  exact measurable_const.min (measurable_const.div
    ((continuous_badDistZ' p₀ β lam ε₀ V Z).measurable.pow_const 2))

/-- The four points `x_j, y_j, x_j - u, y_j - u`: for the dipole `(t, t + u)`, the distances to
the charges of `z = (x_j, y_j)` are the distances from `t` to these points. -/
def gainCentre (z : ℂ × ℂ) (u : ℂ) : Fin 4 → ℂ :=
  ![z.1, z.2, z.1 - u, z.2 - u]

theorem exists_dipoleDist_gain_eq (z : ℂ × ℂ) (u t : ℂ) :
    ∃ l : Fin 4, dipoleDist (t, t + u) z = ‖t - gainCentre z u l‖ := by
  unfold dipoleDist gainCentre
  simp only [Fin.exists_fin_succ, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.exists_fin_zero, or_false]
  rw [show t - (z.1 - u) = t + u - z.1 by ring, show t - (z.2 - u) = t + u - z.2 by ring]
  rcases min_choice (min ‖t - z.1‖ ‖t - z.2‖) (min ‖t + u - z.1‖ ‖t + u - z.2‖) with h | h <;>
    rw [h]
  · rcases min_choice ‖t - z.1‖ ‖t - z.2‖ with h' | h' <;> rw [h']
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · rcases min_choice ‖t + u - z.1‖ ‖t + u - z.2‖ with h' | h' <;> rw [h']
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (by simp)))

end Root

end SmallIntegral
end MultipoleBKT

end
