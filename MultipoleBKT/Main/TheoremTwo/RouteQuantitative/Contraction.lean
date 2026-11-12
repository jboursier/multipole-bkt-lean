/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.TheoremTwo.ProfileFacts
public import MultipoleBKT.RateFunction.Convexity

/-!
# The quantitative contraction and rounding of the LDP ball

The construction in Step 3 of the proof of Theorem 2, with `s = D_p/(Nρ)` and error `2D_p/N`.
-/

@[expose] public section

namespace MultipoleBKT.TheoremTwo

open Finset Set

/-- Contract the ball minimizer toward its center by precisely `D_p/(Nρ)`, then
take floors of the coordinates of size at least two and put the remaining mass in size one. -/
theorem exists_profile_in_ball {p N : ℕ} (hp : 1 ≤ p) (hN : 1 ≤ N)
    {γ η : Fin p → ℝ} (hγ : γ ∈ simplex p 0) (hη : η ∈ simplex p 0)
    {ρ : ℝ} (hρ : 0 < ρ) (hηγ : ‖η - γ‖ ≤ ρ) (hmargin : roundingRadius p ≤ N * ρ) :
    ∃ n : Fin p → ℕ, ∑ i : Fin p, ((i : ℕ) + 1) * n i = N ∧
      (∀ i : Fin p, 1 ≤ (i : ℕ) → (n i : ℝ) ≤ N * (γ i + ρ)) ∧
      ‖(fun i => (n i : ℝ) / N) - γ‖ ≤ ρ ∧
      ‖(fun i => (n i : ℝ) / N) - η‖ ≤ 2 * roundingRadius p / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hD : 0 < roundingRadius p := lt_of_lt_of_le zero_lt_one (one_le_roundingRadius hp)
  let s := roundingRadius p / ((N : ℝ) * ρ)
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := (div_le_one (mul_pos hN0 hρ)).mpr hmargin
  have hsρ : s * ρ = roundingRadius p / N := by dsimp [s]; field_simp
  let η' : Fin p → ℝ := η + s • (γ - η)
  have hη' : η' ∈ simplex p 0 :=
    (convex_simplex 0).add_smul_sub_mem hη hγ ⟨hs0, hs1⟩
  have hηγ' : ‖η' - γ‖ ≤ (1 - s) * ρ := by
    have hid : η' - γ = (1 - s) • (η - γ) := by dsimp [η']; module
    rw [hid, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    exact mul_le_mul_of_nonneg_left hηγ (by linarith)
  have hηη' : ‖η' - η‖ ≤ roundingRadius p / N := by
    have hid : η' - η = s • (γ - η) := by dsimp [η']; abel
    rw [hid, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0, norm_sub_rev, ← hsρ]
    exact mul_le_mul_of_nonneg_left hηγ hs0
  obtain ⟨n, hn, hnle, hnclose⟩ := exists_profile_sharp hp hη' hN
  let v : Fin p → ℝ := fun i => (n i : ℝ) / N
  have hv : ‖v - η'‖ ≤ roundingRadius p / N :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => by
      rw [Real.norm_eq_abs, Pi.sub_apply]; exact hnclose i
  have hvγ : ‖v - γ‖ ≤ ρ := by
    calc ‖v - γ‖ = ‖(v - η') + (η' - γ)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖v - η'‖ + ‖η' - γ‖ := norm_add_le _ _
      _ ≤ roundingRadius p / N + (1 - s) * ρ := add_le_add hv hηγ'
      _ = ρ := by rw [← hsρ]; ring
  have hvη : ‖v - η‖ ≤ 2 * roundingRadius p / N := by
    calc ‖v - η‖ = ‖(v - η') + (η' - η)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖v - η'‖ + ‖η' - η‖ := norm_add_le _ _
      _ ≤ roundingRadius p / N + roundingRadius p / N := add_le_add hv hηη'
      _ = 2 * roundingRadius p / N := by ring
  refine ⟨n, hn, ?_, hvγ, hvη⟩
  intro i hi
  have hcoord : η' i - γ i ≤ ρ := by
    have hc := norm_le_pi_norm (η' - γ) i
    rw [Real.norm_eq_abs, Pi.sub_apply] at hc
    have hr : (1 - s) * ρ ≤ ρ := by nlinarith
    exact (le_abs_self _).trans (hc.trans (hηγ'.trans hr))
  exact (hnle i hi).trans (mul_le_mul_of_nonneg_left (by linarith) hN0.le)

end MultipoleBKT.TheoremTwo

end
