/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.Regularity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integrating along both dipoles

See (3.38).
Two applications of the fundamental theorem of calculus identify the second
difference with the integral of the continuous classical Hessian.
-/

@[expose] public section

open MeasureTheory Set

namespace MultipoleBKT.RouteMixed

/-- The fundamental theorem of calculus along an affine segment. -/
theorem integral_fderiv_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℂ → E} (hd : Differentiable ℝ f)
    (hc : Continuous (fderiv ℝ f)) (a h : ℂ) (u v : ℝ) :
    (∫ t in u..v, fderiv ℝ f (a + t • h) h) = f (a + v • h) - f (a + u • h) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _
    apply (hd _).hasFDerivAt.comp_hasDerivAt t
    simpa using ((hasDerivAt_id t).smul_const h |>.const_add a)
  · exact ((hc.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
      continuous_const).intervalIntegrable _ _

/-- Integrate first along `h`, then along `k`, as in (3.38). -/
theorem integral_hessian_rectangle {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f)
    (a h k : ℂ) (u v : ℝ) :
    (∫ t in u..v, ∫ s in u..v, fderiv ℝ (fderiv ℝ f) (a + s • h + t • k) h k) =
      f (a + v • h + v • k) - f (a + v • h + u • k) -
        f (a + u • h + v • k) + f (a + u • h + u • k) := by
  have hd := hf.differentiable (by norm_num)
  have hf' : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hd' := hf'.differentiable (by norm_num)
  have hc' := hf'.continuous
  have hc'' := hf'.continuous_fderiv (by norm_num)
  have hi (t : ℝ) :
      (∫ s in u..v, fderiv ℝ (fderiv ℝ f) (a + s • h + t • k) h k) =
        fderiv ℝ f (a + v • h + t • k) k - fderiv ℝ f (a + u • h + t • k) k := by
    have he := integral_fderiv_line hd' hc'' (a + t • k) h u v
    have hint : IntervalIntegrable (fun s : ℝ => fderiv ℝ (fderiv ℝ f)
        (a + t • k + s • h) h) volume u v :=
      ((hc''.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
        continuous_const).intervalIntegrable u v
    have hh := congrArg (fun L : ℂ →L[ℝ] ℝ => L k) he
    rw [ContinuousLinearMap.intervalIntegral_apply hint] at hh
    simpa only [add_assoc, add_left_comm, add_comm, sub_apply] using hh
  simp_rw [hi]
  rw [intervalIntegral.integral_sub]
  · rw [integral_fderiv_line hd hc', integral_fderiv_line hd hc']
    ring
  · exact ((hc'.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
      continuous_const).intervalIntegrable _ _
  · exact ((hc'.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
      continuous_const).intervalIntegrable _ _

/-- A pointwise bound on the Hessian integrand bounds its double integral.
The centered parameter interval has length one. -/
theorem norm_integral_integral_le {F : ℝ → ℝ → ℝ} {C : ℝ}
    (hF : ∀ s ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), ∀ t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2),
      ‖F s t‖ ≤ C) :
    ‖∫ t in -(1 / 2 : ℝ)..1 / 2, ∫ s in -(1 / 2 : ℝ)..1 / 2, F s t‖ ≤ C := by
  have hi (t : ℝ) (ht : t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
      ‖∫ s in -(1 / 2 : ℝ)..1 / 2, F s t‖ ≤ C := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := -(1 / 2 : ℝ)) (b := 1 / 2)
      (fun s hs => hF s ⟨by simpa using le_of_lt hs.1, by simpa using hs.2⟩ t ht)
    norm_num at hh ⊢
    exact hh
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := -(1 / 2 : ℝ)) (b := 1 / 2)
    (fun t ht => hi t ⟨by simpa using le_of_lt ht.1, by simpa using ht.2⟩)
  norm_num at hh ⊢
  exact hh

/-- Subtract the central Hessian before estimating the double integral.
This is the first-order expansion used after (3.38). -/
theorem norm_integral_integral_sub_const_le {F : ℝ → ℝ → ℝ} {c C : ℝ}
    (hc : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hF : ∀ s ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), ∀ t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2),
      ‖F s t - c‖ ≤ C) :
    ‖(∫ t in -(1 / 2 : ℝ)..1 / 2, ∫ s in -(1 / 2 : ℝ)..1 / 2, F s t) - c‖ ≤ C := by
  have hi (t : ℝ) : IntervalIntegrable (fun s => F s t) volume (-(1 / 2 : ℝ)) (1 / 2) :=
    (hc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  have ho : Continuous (fun t => ∫ s in -(1 / 2 : ℝ)..1 / 2, F s t) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun t s => F s t) (hc.comp continuous_swap) _ _
  have he : (∫ t in -(1 / 2 : ℝ)..1 / 2, ∫ s in -(1 / 2 : ℝ)..1 / 2, F s t - c) =
      (∫ t in -(1 / 2 : ℝ)..1 / 2, ∫ s in -(1 / 2 : ℝ)..1 / 2, F s t) - c := by
    simp_rw [intervalIntegral.integral_sub (hi _) intervalIntegrable_const,
      intervalIntegral.integral_const]
    norm_num
    rw [intervalIntegral.integral_sub (ho.intervalIntegrable _ _) intervalIntegrable_const]
    norm_num
  rw [← he]
  exact norm_integral_integral_le hF

/-- The centered parameter rectangle has displacement at most half the sum
of the two dipole lengths. -/
theorem norm_rectangle_shift_le (h k : ℂ) {s t : ℝ}
    (hs : s ∈ Icc (-(1 / 2 : ℝ)) (1 / 2))
    (ht : t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    ‖s • h + t • k‖ ≤ (‖h‖ + ‖k‖) / 2 := by
  have hs' : |s| ≤ 1 / 2 := abs_le.mpr hs
  have ht' : |t| ≤ 1 / 2 := abs_le.mpr ht
  calc _ ≤ ‖s • h‖ + ‖t • k‖ := norm_add_le _ _
    _ = |s| * ‖h‖ + |t| * ‖k‖ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (‖h‖ + ‖k‖) / 2 := by nlinarith [norm_nonneg h, norm_nonneg k]

end MultipoleBKT.RouteMixed
