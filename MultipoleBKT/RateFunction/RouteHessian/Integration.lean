/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.RateFunction.RouteHessian.Derivatives
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integrating a lower bound for the second derivative

Two applications of the fundamental theorem of calculus give the quadratic lower
bound used for the minimizer segment in Step 5 of the proof of Theorem 2.
Only a compact subsegment with positive coordinates will be differentiated.
-/

@[expose] public section

namespace MultipoleBKT

open Set MeasureTheory intervalIntegral

/-- Internal calculus estimate: integrate `f'' ≥ c` first to bound `f'`, then to bound `f`.
No continuity or integrability of `f''` is needed for the lower integral comparison. -/
theorem quadratic_lower_of_hasDerivAt2 {f f' f'' : ℝ → ℝ} {s c : ℝ} (hs : 0 ≤ s)
    (h1 : ∀ t ∈ Icc (0 : ℝ) s, HasDerivAt f (f' t) t)
    (h2 : ∀ t ∈ Icc (0 : ℝ) s, HasDerivAt f' (f'' t) t)
    (hcurv : ∀ t ∈ Icc (0 : ℝ) s, c ≤ f'' t) :
    f 0 + f' 0 * s + c * s ^ 2 / 2 ≤ f s := by
  have hfirst : ∀ t ∈ Icc (0 : ℝ) s, f' 0 + c * t ≤ f' t := by
    intro t ht
    have h := integral_le_sub_of_hasDeriv_right_of_le ht.1
      (fun u hu => (h2 u ⟨hu.1, hu.2.trans ht.2⟩).continuousAt.continuousWithinAt)
      (fun u hu => (h2 u ⟨hu.1.le, hu.2.le.trans ht.2⟩).hasDerivWithinAt)
      (continuous_const.integrableOn_Icc : IntegrableOn (fun _ : ℝ => c) (Icc 0 t))
      (fun u hu => hcurv u ⟨hu.1.le, hu.2.le.trans ht.2⟩)
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
    nlinarith
  have h := integral_le_sub_of_hasDeriv_right_of_le hs
    (fun t ht => (h1 t ht).continuousAt.continuousWithinAt)
    (fun t ht => (h1 t (Ioo_subset_Icc_self ht)).hasDerivWithinAt)
    ((continuous_const.add (continuous_const.mul continuous_id)).integrableOn_Icc :
      IntegrableOn (fun t : ℝ => f' 0 + c * t) (Icc 0 s))
    (fun t ht => hfirst t (Ioo_subset_Icc_self ht))
  have hint : IntervalIntegrable (fun t : ℝ => c * t) volume 0 s :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 s
  rw [intervalIntegral.integral_add intervalIntegrable_const hint,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, integral_id] at h
  simp only [sub_zero, smul_eq_mul, zero_pow (by omega : (2 : ℕ) ≠ 0)] at h
  nlinarith

end MultipoleBKT

end
