/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.RouteLocal.RadiusChange

/-!
# Quadratic comparison for the four bad–bad classes

The paper: (3.41),
 and its application in Lemma 5.12.
Use the common-radius insertion, then translation and radius change.
-/

@[expose] public section

namespace MultipoleBKT.UpperBound

variable {χ : ℂ → ℝ} {N : ℕ} {lam : ℝ}

/-- The smoothing part of (3.41), with the quadratic radius error retained. -/
theorem abs_halfInteractionPlus_sub_le_sq (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    {τp τm : Fin N → ℝ} (d : Fin N → ℂ × ℂ) {i j : Fin N}
    (hpi : 0 < τp i) (hmi : 0 < τm i) (hj : 0 < τp j) :
    |halfInteractionPlus χ lam τp τm d i j -
        (smearedKernel χ lam ((d i).1 - (d j).1) - smearedKernel χ lam ((d i).2 - (d j).1))| ≤
      Real.sqrt (Real.pi * M) * ‖(d i).1 - (d i).2‖ / τp j +
        6 * Real.pi * M * max (τp i) (τm i) ^ 2 / (τp j) ^ 2 := by
  rw [halfInteractionPlus_eq, add_sub_cancel_left,
    RouteLocal.common_radius_insertion hχ (τm i) (τp i) (τp j) (d i).2 (d i).1 (d j).1]
  have ht := RouteLocal.abs_translation_le hχ hM hmi hj (d i).2 (d i).1 (d j).1
  rw [norm_sub_rev] at ht
  have hr := RouteLocal.abs_radius_change_le hχ hM hmi hpi hj (d i).1 (d j).1
  rw [max_comm (τm i)] at hr
  exact (abs_add_le _ _).trans (add_le_add ht hr)

end MultipoleBKT.UpperBound

end
