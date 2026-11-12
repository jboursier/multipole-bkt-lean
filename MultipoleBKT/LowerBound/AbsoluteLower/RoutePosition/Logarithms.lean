/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Position

/-!
# The literal logarithms left by the spatial integral

The proof of Lemma 4.58. On the radial cutoff,
`1 + log⁺(17h/ρ)` is bounded by a fixed multiple of `log(17h/r)`.
The original radius r is positive on the relevant support. Zero radii
will be handled by the vanishing radial weight in the integral theorem.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RoutePosition

open MeasureTheory Set Finset Limits

/-- Convert the regularized edge logarithm to the paper's logarithm.
The coefficient depends only on the numerical cutoff 17. -/
theorem ell_le_source_log {h r ρ : ℝ} (hr : 0 < r) (hrh : r ≤ h) (hrρ : r ≤ ρ) :
    ell (17 * h) ρ ≤ (1 + (Real.log 17)⁻¹) * Real.log (17 * h / r) := by
  have h17 : 0 < Real.log 17 := Real.log_pos (by norm_num)
  have hratio : (17 : ℝ) ≤ 17 * h / r := (le_div_iff₀ hr).mpr (by linarith)
  have hlog : Real.log 17 ≤ Real.log (17 * h / r) :=
    Real.log_le_log (by norm_num) hratio
  have hinv : 1 ≤ (Real.log 17)⁻¹ * Real.log (17 * h / r) := by
    rw [inv_mul_eq_div, le_div_iff₀ h17]
    simpa only [one_mul] using hlog
  have hh : 0 < h := hr.trans_le hrh
  calc
    ell (17 * h) ρ ≤ ell (17 * h) r := ell_anti (by positivity) hr hrρ
    _ = 1 + Real.log (17 * h / r) := by
      unfold ell
      rw [max_eq_left (h17.le.trans hlog)]
    _ ≤ _ := by nlinarith

/-- The paper's single-dipole radial weight, including its cutoff. -/
noncomputable def sourceWeight (χ : ℂ → ℝ) (β lam h a : ℝ) (u : ℂ) : ℝ :=
  Real.exp (β * smearedKernel χ lam u) *
    (Metric.closedBall (0 : ℂ) h).indicator (fun u => (h / ‖u‖) ^ a) u

theorem sourceWeight_nonneg (χ : ℂ → ℝ) (β lam : ℝ) {h : ℝ} (hh : 0 ≤ h)
    (a : ℝ) (u : ℂ) : 0 ≤ sourceWeight χ β lam h a u :=
  mul_nonneg (Real.exp_pos _).le (indicator_nonneg (fun _ _ =>
    Real.rpow_nonneg (div_nonneg hh (norm_nonneg _)) _) u)

/-- Removing the numerical factor 17 from each radial weight costs `17^a`. -/
theorem dipoleWeight_eq_sourceWeight (χ : ℂ → ℝ) (β lam : ℝ) {h : ℝ}
    (hh : 0 ≤ h) (a : ℝ) (u : ℂ) :
    dipoleWeight χ β lam h a u = (17 : ℝ) ^ a * sourceWeight χ β lam h a u := by
  unfold dipoleWeight sourceWeight
  by_cases hu : u ∈ Metric.closedBall (0 : ℂ) h
  · rw [indicator_of_mem hu, indicator_of_mem hu,
      mul_div_assoc, Real.mul_rpow (by norm_num) (div_nonneg hh (norm_nonneg _))]
    ring
  · rw [indicator_of_notMem hu, indicator_of_notMem hu]
    ring

end MultipoleBKT.AbsoluteLower.RoutePosition

end
