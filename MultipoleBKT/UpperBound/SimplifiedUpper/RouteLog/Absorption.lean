/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.SimplifiedUpper.RouteLog.Factors
public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Euler

/-!
# Absorption of the predecessor logarithms before integration

The paper: proof of
Lemma 4.57, reused in Lemma 5.37.
Apply `(1 + log_M(17t))² ≤ C_M t^(1/M)` to each positive radius.
-/

@[expose] public section

namespace MultipoleBKT.UpperBound.SimplifiedUpper

open Finset AbsoluteLower
open scoped Classical

/-- The product form of proof of Lemma 4.57, retaining the existing radial power.
The coefficient is independent of the cutoff, radii and radial exponent. -/
theorem exists_radLogProduct_le {M : ℝ} (hM : 1 < M) :
    ∃ CL : ℝ, 1 ≤ CL ∧ ∀ (W : Finset ℕ) (c : ℕ → ℂ × ℂ) (ε₀ R a : ℝ),
      (∀ i ∈ W, 0 < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) →
      (∏ i ∈ W, (ε₀ * R / ‖(c i).1 - (c i).2‖) ^ (a / M) *
        (1 + Real.logb M (17 * ε₀ * R / ‖(c i).1 - (c i).2‖)) ^ 2) ≤
      CL ^ W.card * ∏ i ∈ W, (ε₀ * R / ‖(c i).1 - (c i).2‖) ^ ((a + 1) / M) := by
  obtain ⟨CL, hCL, hlog⟩ := exists_one_add_logb_sq_le hM
  refine ⟨CL, hCL, fun W c ε₀ R a hr => ?_⟩
  calc _ ≤ ∏ i ∈ W, CL * (ε₀ * R / ‖(c i).1 - (c i).2‖) ^ ((a + 1) / M) := by
          refine prod_le_prod₀ (fun i hi => mul_nonneg (Real.rpow_nonneg
            (div_nonneg ((hr i hi).1.le.trans (hr i hi).2) (norm_nonneg _)) _) (sq_nonneg _))
            fun i hi => ?_
          let t := ε₀ * R / ‖(c i).1 - (c i).2‖
          have ht : 1 ≤ t := (one_le_div (hr i hi).1).2 (hr i hi).2
          have ht0 : 0 < t := zero_lt_one.trans_le ht
          have hl := hlog t ht
          have heq : 17 * t = 17 * ε₀ * R / ‖(c i).1 - (c i).2‖ := by dsimp [t]; ring
          rw [heq] at hl
          calc _ ≤ t ^ (a / M) * (CL * t ^ (1 / M)) :=
                  mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg ht0.le _)
            _ = CL * t ^ ((a + 1) / M) := by
                  rw [mul_left_comm, ← Real.rpow_add ht0, ← add_div]
      _ = _ := by rw [prod_mul_distrib, prod_const]

end MultipoleBKT.UpperBound.SimplifiedUpper

end
