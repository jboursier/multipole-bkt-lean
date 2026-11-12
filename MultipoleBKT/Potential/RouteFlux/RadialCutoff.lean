/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Radial tests for weak Stokes's formula

See Lemmas 3.1 and 3.2 of the paper.
The tests equal one inside a disc and zero beyond a shrinking annulus.
Smooth transitions make them admissible in the weak Poisson identity directly.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped RealInnerProductSpace

namespace MultipoleBKT.RouteFlux

/-- A smooth radial cutoff written as a function of squared distance. -/
noncomputable def fluxCutoff (r h : ℝ) (x : ℂ) : ℝ :=
  1 - Real.smoothTransition ((‖x‖ ^ 2 - r ^ 2) / ((r + h) ^ 2 - r ^ 2))

/-- The same cutoff on the real radius. -/
noncomputable def fluxProfile (r h t : ℝ) : ℝ :=
  1 - Real.smoothTransition ((t ^ 2 - r ^ 2) / ((r + h) ^ 2 - r ^ 2))

theorem contDiff_fluxCutoff (r h : ℝ) : ContDiff ℝ 1 (fluxCutoff r h) :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((contDiff_norm_sq ℝ).sub contDiff_const |>.div_const _))

theorem contDiff_fluxProfile (r h : ℝ) : ContDiff ℝ 2 (fluxProfile r h) :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((contDiff_id.pow 2).sub contDiff_const |>.div_const _))

private theorem width_pos {r h : ℝ} (hr : 0 < r) (hh : 0 < h) :
    0 < (r + h) ^ 2 - r ^ 2 := by nlinarith

theorem fluxProfile_eq_one {r h t : ℝ} (hr : 0 < r) (hh : 0 < h)
    (ht : |t| ≤ r) : fluxProfile r h t = 1 := by
  rw [fluxProfile, Real.smoothTransition.zero_of_nonpos]
  · ring
  · apply div_nonpos_of_nonpos_of_nonneg _ (width_pos hr hh).le
    nlinarith [sq_abs t, mul_nonneg (sub_nonneg.mpr ht) (show 0 ≤ r + |t| by positivity)]

theorem fluxProfile_eq_zero {r h t : ℝ} (hr : 0 < r) (hh : 0 < h)
    (ht : r + h ≤ |t|) : fluxProfile r h t = 0 := by
  rw [fluxProfile, Real.smoothTransition.one_of_one_le]
  · ring
  · apply (le_div_iff₀ (width_pos hr hh)).mpr
    nlinarith [sq_abs t, abs_nonneg t]

theorem fluxCutoff_eq_profile (r h : ℝ) (x : ℂ) :
    fluxCutoff r h x = fluxProfile r h ‖x‖ := rfl

theorem hasCompactSupport_fluxCutoff {r h : ℝ} (hr : 0 < r) (hh : 0 < h) :
    HasCompactSupport (fluxCutoff r h) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) (r + h))
  intro x hx
  by_contra hn
  have hn' : r + h ≤ ‖x‖ := le_of_lt (by simpa using hn)
  exact hx (by rw [fluxCutoff_eq_profile, fluxProfile_eq_zero hr hh (by simpa using hn')])

theorem fluxCutoff_mem_Icc (r h : ℝ) (x : ℂ) : fluxCutoff r h x ∈ Icc (0 : ℝ) 1 := by
  constructor <;> dsimp [fluxCutoff]
  · linarith [Real.smoothTransition.le_one ((‖x‖ ^ 2 - r ^ 2) / ((r + h) ^ 2 - r ^ 2))]
  · linarith [Real.smoothTransition.nonneg ((‖x‖ ^ 2 - r ^ 2) / ((r + h) ^ 2 - r ^ 2))]

private theorem deriv_fluxProfile (r h t : ℝ) :
    deriv (fluxProfile r h) t =
      -(deriv Real.smoothTransition ((t ^ 2 - r ^ 2) / ((r + h) ^ 2 - r ^ 2)) *
        (2 * t / ((r + h) ^ 2 - r ^ 2))) := by
  unfold fluxProfile
  simpa only [Function.comp_def, Pi.pow_apply, id_eq, Nat.cast_ofNat,
    pow_one, mul_one, Nat.reduceSub] using (((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt.comp t
    (((hasDerivAt_id t).pow 2 |>.sub_const (r ^ 2)).div_const ((r + h) ^ 2 - r ^ 2))).const_sub 1 |>.deriv

theorem deriv_fluxProfile_nonpos {r h t : ℝ} (hr : 0 < r) (hh : 0 < h) (ht : 0 ≤ t) :
    deriv (fluxProfile r h) t ≤ 0 := by
  rw [deriv_fluxProfile]
  exact neg_nonpos.mpr (mul_nonneg (Real.smoothTransition.monotone.deriv_nonneg)
    (div_nonneg (by positivity) (width_pos hr hh).le))

theorem deriv_fluxProfile_eq_zero {r h t : ℝ} (hr : 0 < r) (hh : 0 < h)
    (ht : t < r ∨ r + h < t) (ht0 : 0 < t) : deriv (fluxProfile r h) t = 0 := by
  rcases ht with ht | ht
  · have he : fluxProfile r h =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [eventually_lt_nhds ht, eventually_gt_nhds ht0] with s hs hs0
      exact fluxProfile_eq_one hr hh (by rw [abs_of_pos hs0]; exact hs.le)
    exact he.deriv_eq.trans (deriv_const t 1)
  · have he : fluxProfile r h =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [eventually_gt_nhds ht] with s hs
      exact fluxProfile_eq_zero hr hh (by rw [abs_of_pos (by linarith)]; exact hs.le)
    exact he.deriv_eq.trans (deriv_const t 0)

private theorem fderiv_fluxCutoff (r h : ℝ) (x v : ℂ) :
    fderiv ℝ (fluxCutoff r h) x v =
      -(deriv Real.smoothTransition ((‖x‖ ^ 2 - r ^ 2) / ((r + h) ^ 2 - r ^ 2)) *
        (2 * ⟪x, v⟫ / ((r + h) ^ 2 - r ^ 2))) := by
  have he := (((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt.comp_hasFDerivAt x
    (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.sub_const (r ^ 2)).mul_const (((r + h) ^ 2 - r ^ 2)⁻¹))).const_sub 1
  simp only [Function.comp_def] at he
  unfold fluxCutoff
  simp_rw [div_eq_mul_inv]
  rw [he.fderiv]
  simp only [neg_apply, smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  ring

/-- The derivative of the cutoff has total mass minus one. -/
theorem integral_deriv_fluxProfile {r h R : ℝ} (hr : 0 < r) (hh : 0 < h)
    (hR : r + h ≤ R) : ∫ t in (0 : ℝ)..R, deriv (fluxProfile r h) t = -1 := by
  rw [intervalIntegral.integral_deriv_eq_sub
    (fun t _ => (contDiff_fluxProfile r h).differentiable (by norm_num) t)
    (((contDiff_fluxProfile r h).continuous_deriv (by norm_num)).intervalIntegrable 0 R),
    fluxProfile_eq_zero hr hh (hR.trans (le_abs_self R)),
    fluxProfile_eq_one hr hh (by simpa using hr.le)]
  ring

/-- Polar Jacobian cancellation for the radial test. -/
theorem radius_mul_fderiv_fluxCutoff (r h : ℝ) {t : ℝ} (ht : 0 ≤ t) (θ : ℝ) (v : ℂ) :
    t * fderiv ℝ (fluxCutoff r h) (circleMap 0 t θ) v =
      deriv (fluxProfile r h) t * ⟪v, circleMap 0 t θ⟫ := by
  rw [fderiv_fluxCutoff, deriv_fluxProfile, norm_circleMap_zero, abs_of_nonneg ht,
    real_inner_comm]
  ring

/-- The differential vanishes beyond the outer edge of the annulus. -/
theorem fderiv_fluxCutoff_eq_zero {r h : ℝ} (hr : 0 < r) (hh : 0 < h) {x : ℂ}
    (hx : r + h < ‖x‖) : fderiv ℝ (fluxCutoff r h) x = 0 := by
  have he : fluxCutoff r h =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [(continuous_norm.tendsto x).eventually (lt_mem_nhds hx)] with y hy
    rw [fluxCutoff_eq_profile, fluxProfile_eq_zero hr hh (by simpa using hy.le)]
  exact he.fderiv_eq.trans (by simp)

end MultipoleBKT.RouteFlux

end
