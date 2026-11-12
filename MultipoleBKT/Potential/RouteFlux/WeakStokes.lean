/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.RouteFlux.RadialCutoff
import TwoComponentCoulomb.Potential.DiscField
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Weak Stokes's formula on a disc

See Lemmas 3.1 and 3.2 of the paper.
Radial smooth tests converge to the disc indicator. Their differential pairs
with a continuous field to give minus its circle flux. This is the weak form
of Stokes's formula and requires no derivative of the field.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology Complex
open scoped RealInnerProductSpace

namespace MultipoleBKT.RouteFlux

/-- Outward flux through a circle about the origin. For positive radius,
the arc length factor cancels the denominator in the unit normal. -/
noncomputable def circleFlux (F : ℂ → ℂ) (r : ℝ) : ℝ :=
  ∫ θ in Ioo (-Real.pi) Real.pi, ⟪F (circleMap 0 r θ), circleMap 0 r θ⟫

/-- Continuity of flux uses only continuity of the field. -/
private theorem continuous_circleFlux {F : ℂ → ℂ} (hF : Continuous F) : Continuous (circleFlux F) := by
  have he : circleFlux F = fun r =>
      ∫ θ in Icc (-Real.pi) Real.pi, ⟪F (circleMap 0 r θ), circleMap 0 r θ⟫ := by
    funext r
    exact integral_Icc_eq_integral_Ioo.symm
  rw [he]
  apply continuous_parametric_integral_of_continuous (s := Icc (-Real.pi) Real.pi)
    (hs := isCompact_Icc)
  have hc : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
    simp only [circleMap, zero_add]
    fun_prop
  exact (hF.comp hc).inner hc

/-- In polar coordinates the weak test is the derivative of a radial cutoff
paired with the circle flux. -/
private theorem integral_fderiv_fluxCutoff {F : ℂ → ℂ} (hF : Continuous F) {r h R : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hR : r + h < R) :
    ∫ x, fderiv ℝ (fluxCutoff r h) x (F x) =
      ∫ t in (0 : ℝ)..R, deriv (fluxProfile r h) t * circleFlux F t := by
  have hg : Continuous (fun x => fderiv ℝ (fluxCutoff r h) x (F x)) :=
    ((contDiff_fluxCutoff r h).continuous_fderiv one_ne_zero).clm_apply hF
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball (0 : ℂ) R) (fun x hx => by
    have hx' : R ≤ ‖x‖ := by simpa using hx
    rw [fderiv_fluxCutoff_eq_zero hr hh (hR.trans_le hx')]
    simp), TwoComponentCoulomb.setIntegral_ball_zero_eq_polar_of_measurable
      hg.measurable ((hg.continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : ℂ) R)).mono_set ball_subset_closedBall),
    intervalIntegral.integral_of_le (by linarith : 0 ≤ R), integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  rw [smul_eq_mul, ← integral_const_mul]
  calc
    (∫ θ in Ioo (-Real.pi) Real.pi,
      t * fderiv ℝ (fluxCutoff r h) (circleMap 0 t θ) (F (circleMap 0 t θ))) =
        ∫ θ in Ioo (-Real.pi) Real.pi,
          deriv (fluxProfile r h) t * ⟪F (circleMap 0 t θ), circleMap 0 t θ⟫ := by
            apply integral_congr_ae
            exact Eventually.of_forall fun θ => radius_mul_fderiv_fluxCutoff r h ht.1.le θ _
    _ = deriv (fluxProfile r h) t * circleFlux F t := by rw [integral_const_mul, circleFlux]

/-- A finite source with no mass on the boundary sees the radial tests converge
to its enclosed mass. This applies to bounded measurable densities. -/
theorem tendsto_integral_fluxCutoff (μ : Measure ℂ) [IsFiniteMeasure μ] {r : ℝ}
    (hr : 0 < r) (hμ : ∀ᵐ x ∂μ, ‖x‖ ≠ r) :
    Tendsto (fun h => ∫ x, fluxCutoff r h x ∂μ) (𝓝[>] 0) (𝓝 (μ.real (ball 0 r))) := by
  have ht : Tendsto (fun h => ∫ x, fluxCutoff r h x ∂μ) (𝓝[>] 0)
      (𝓝 (∫ x, (ball (0 : ℂ) r).indicator (fun _ => (1 : ℝ)) x ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
    · exact Eventually.of_forall fun h => (contDiff_fluxCutoff r h).continuous.aestronglyMeasurable
    · exact Eventually.of_forall fun h => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (fluxCutoff_mem_Icc r h x).1]
        exact (fluxCutoff_mem_Icc r h x).2
    · exact integrable_const 1
    · filter_upwards [hμ] with x hx
      rcases lt_or_gt_of_ne hx with hx | hx
      · rw [indicator_of_mem (mem_ball_zero_iff.mpr hx)]
        apply tendsto_const_nhds.congr'
        filter_upwards [self_mem_nhdsWithin] with h hh
        rw [fluxCutoff_eq_profile, fluxProfile_eq_one hr hh (by simpa using hx.le)]
      · rw [indicator_of_notMem (by simpa using hx.not_gt)]
        apply tendsto_const_nhds.congr'
        filter_upwards [self_mem_nhdsWithin,
          (eventually_lt_nhds (show 0 < ‖x‖ - r by linarith)).filter_mono nhdsWithin_le_nhds]
          with h hh hx'
        rw [fluxCutoff_eq_profile, fluxProfile_eq_zero hr hh (by
          rw [abs_of_nonneg (norm_nonneg x)]; linarith)]
  rw [integral_indicator measurableSet_ball, setIntegral_const, smul_eq_mul, mul_one] at ht
  exact ht

private theorem tendsto_integral_deriv_fluxProfile_mul {G : ℝ → ℝ} (hG : Continuous G)
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun h => ∫ t in (0 : ℝ)..(r + 1), deriv (fluxProfile r h) t * G t)
      (𝓝[>] 0) (𝓝 (-G r)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hG.continuousAt (ε / 2) (by positivity)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (lt_min hδ (by norm_num : (0 : ℝ) < 1))).filter_mono nhdsWithin_le_nhds]
      with h hh hsmall
  have hR : r + h ≤ r + 1 := by linarith [hsmall.trans_le (min_le_right δ 1)]
  have hi : IntervalIntegrable (deriv (fluxProfile r h)) volume 0 (r + 1) :=
    ((contDiff_fluxProfile r h).continuous_deriv (by norm_num)).intervalIntegrable _ _
  have hig : IntervalIntegrable (fun t => deriv (fluxProfile r h) t * G t)
      volume 0 (r + 1) :=
    (((contDiff_fluxProfile r h).continuous_deriv (by norm_num)).mul hG).intervalIntegrable _ _
  have he : (∫ t in (0 : ℝ)..(r + 1), deriv (fluxProfile r h) t * G t) - -G r =
      ∫ t in (0 : ℝ)..(r + 1), deriv (fluxProfile r h) t * (G t - G r) := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub hig (hi.mul_const _),
      intervalIntegral.integral_mul_const, integral_deriv_fluxProfile hr hh hR]
    ring
  rw [dist_eq_norm, he]
  have hb : ∀ t ∈ Ioc (0 : ℝ) (r + 1),
      ‖deriv (fluxProfile r h) t * (G t - G r)‖ ≤
        -deriv (fluxProfile r h) t * (ε / 2) := by
    intro t ht
    by_cases ht' : t < r ∨ r + h < t
    · rw [deriv_fluxProfile_eq_zero hr hh ht' ht.1]
      simp
    · have ht' : r ≤ t ∧ t ≤ r + h := by simpa only [not_or, not_lt] using ht'
      have hd' : dist t r < δ := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht'.1)]
        linarith [hsmall.trans_le (min_le_left δ 1)]
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonpos (deriv_fluxProfile_nonpos hr hh ht.1.le)]
      exact mul_le_mul_of_nonneg_left (le_of_lt (by simpa only [dist_eq_norm] using hd hd'))
        (neg_nonneg.mpr (deriv_fluxProfile_nonpos hr hh ht.1.le))
  calc
    ‖∫ t in (0 : ℝ)..(r + 1), deriv (fluxProfile r h) t * (G t - G r)‖ ≤
        ∫ t in (0 : ℝ)..(r + 1), -deriv (fluxProfile r h) t * (ε / 2) :=
      intervalIntegral.norm_integral_le_of_norm_le (by linarith)
        (Eventually.of_forall hb) (hi.neg.mul_const _)
    _ = ε / 2 := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_neg,
        integral_deriv_fluxProfile hr hh hR]
      ring
    _ < ε := by linarith

/-- The differential of the radial test converges to minus the outward flux.
This is the boundary limit in Stokes's formula for a continuous weak field. -/
theorem tendsto_integral_fderiv_fluxCutoff {F : ℂ → ℂ} (hF : Continuous F) {r : ℝ}
    (hr : 0 < r) :
    Tendsto (fun h => ∫ x, fderiv ℝ (fluxCutoff r h) x (F x))
      (𝓝[>] 0) (𝓝 (-circleFlux F r)) := by
  apply (tendsto_integral_deriv_fluxProfile_mul (continuous_circleFlux hF) hr).congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with h hh h1
  exact (integral_fderiv_fluxCutoff hF hr hh (by linarith : r + h < r + 1)).symm

end MultipoleBKT.RouteFlux

end
