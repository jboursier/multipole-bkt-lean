/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.RouteFlux.CircleFlux

/-!
# Recovering the radial field from flux

See Lemmas 3.1 and 3.2 of the paper.

Rotation invariance makes the normal component constant on a circle. Stokes's
flux identity then identifies it with minus enclosed mass divided by radius.
Scaling the enclosed mass gives the flux sign for two different smoothing radii.
Neither the logarithmic Newton formula nor classical second derivatives enter.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace MultipoleBKT.RouteFlux

variable {χ : ℂ → ℝ} {α η : ℝ}

private theorem pointField_mul_unit {u : ℂ} (hu : ‖u‖ = 1) (w : ℂ) :
    pointField (u * w) = u * pointField w := by
  simp only [pointField, norm_mul, hu, one_mul, Complex.real_smul]
  ring

/-- The convolution field respects rotations, before any regularity assertion. -/
theorem convolvedField_mul_unit (hχ : IsMollifier χ) (α : ℝ) {u : ℂ}
    (hu : ‖u‖ = 1) (x : ℂ) :
    convolvedField χ 0 α (u * x) = u * convolvedField χ 0 α x := by
  unfold convolvedField
  have he := integral_comp_rotate_smearedCharge' hχ 0 α hu
    (fun y => pointField (u * x - y))
  simp only [sub_zero, zero_add] at he
  rw [← he]
  simp_rw [← mul_sub, pointField_mul_unit hu]
  rw [integral_const_mul]

private theorem inner_mul_unit {u : ℂ} (hu : ‖u‖ = 1) (v w : ℂ) :
    ⟪u * v, u * w⟫ = ⟪v, w⟫ := by
  rw [Complex.inner, Complex.inner, map_mul]
  have he : u * starRingEnd ℂ u = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
    norm_num
  have he' : u * w * (starRingEnd ℂ u * starRingEnd ℂ v) = w * starRingEnd ℂ v := by
    calc u * w * (starRingEnd ℂ u * starRingEnd ℂ v) =
        (u * starRingEnd ℂ u) * (w * starRingEnd ℂ v) := by ring
      _ = w * starRingEnd ℂ v := by rw [he, one_mul]
  rw [he']

/-- The normal flux density is constant on a circle by rotation invariance. -/
theorem normalComponent_circleMap (hχ : IsMollifier χ) (α r θ : ℝ) :
    ⟪convolvedField χ 0 α (circleMap 0 r θ), circleMap 0 r θ⟫ =
      r * ⟪convolvedField χ 0 α (r : ℂ), (1 : ℂ)⟫ := by
  have he : circleMap 0 r θ = Complex.exp (θ * Complex.I) * (r : ℂ) := by
    simp [circleMap, mul_comm]
  rw [he, convolvedField_mul_unit hχ α (Complex.norm_exp_ofReal_mul_I θ),
    inner_mul_unit (Complex.norm_exp_ofReal_mul_I θ)]
  have hr : (r : ℂ) = r • (1 : ℂ) := by simp [Complex.real_smul]
  rw [hr, real_inner_smul_right]

/-- The radial component is obtained from flux: `-u'(r) = m(r) / r`.
Here the derivative is represented by the convolved point field, so this result
is available before identifying the classical gradient of the potential. -/
theorem radialComponent_convolvedField (hχ : IsMollifier χ) (hα : 0 < α)
    {r : ℝ} (hr : 0 < r) :
    ⟪convolvedField χ 0 α (r : ℂ), (1 : ℂ)⟫ = -massProfile χ α r / r := by
  have hf := circleFlux_convolvedField hχ 0 hα hr
  unfold circleFlux at hf
  simp_rw [normalComponent_circleMap hχ] at hf
  rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos]),
    smul_eq_mul] at hf
  change (Real.pi - -Real.pi) * (r * _) = -(2 * Real.pi) * massProfile χ α r at hf
  apply (eq_div_iff hr.ne').mpr
  nlinarith [Real.pi_pos]

/-- Scaling of enclosed mass, the change of variables in Lemma 3.2. -/
theorem massProfile_scale (hχ : IsMollifier χ) (hα : 0 < α) (r : ℝ) :
    massProfile χ α r = massProfile χ 1 (r / α) := by
  unfold massProfile
  rw [measureReal_def, measureReal_def, smearedCharge_eq_map hχ 0 hα,
    Measure.map_apply (by fun_prop) measurableSet_ball]
  congr 1
  congr 1
  ext x
  simp only [mem_preimage, zero_add, mem_ball_zero_iff, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα]
  rw [lt_div_iff₀ hα, mul_comm]

/-- Smaller smoothing radii enclose more mass in every disc. -/
theorem massProfile_le_of_scale_le (hχ : IsMollifier χ) (hα : 0 < α) (hαη : α ≤ η)
    {r : ℝ} (hr : 0 ≤ r) : massProfile χ η r ≤ massProfile χ α r := by
  rw [massProfile_scale hχ (hα.trans_le hαη), massProfile_scale hχ hα]
  exact massProfile_mono hχ 1 (div_le_div_of_nonneg_left hr hα hαη)

/-- The nonpositive flux of the difference of two smoothed potentials in Lemma 3.2. -/
theorem circleFlux_sub_nonpos (hχ : IsMollifier χ) (hα : 0 < α) (hαη : α ≤ η)
    {r : ℝ} (hr : 0 < r) :
    circleFlux (convolvedField χ 0 α) r - circleFlux (convolvedField χ 0 η) r ≤ 0 := by
  rw [circleFlux_sub_convolvedField hχ 0 hα (hα.trans_le hαη) hr]
  have hm := massProfile_le_of_scale_le hχ hα hαη hr.le
  change massProfile χ η r ≤ massProfile χ α r at hm
  change -(2 * Real.pi) * (massProfile χ α r - massProfile χ η r) ≤ 0
  nlinarith [Real.pi_pos]

/-- The radial derivative of the difference is nonpositive, as deduced from flux
in Lemma 3.2. This statement concerns the convolution fields, independently
of the later identification of these fields with classical gradients. -/
theorem radialComponent_sub_nonpos (hχ : IsMollifier χ) (hα : 0 < α) (hαη : α ≤ η)
    {r : ℝ} (hr : 0 < r) :
    ⟪convolvedField χ 0 α (r : ℂ), (1 : ℂ)⟫ -
      ⟪convolvedField χ 0 η (r : ℂ), (1 : ℂ)⟫ ≤ 0 := by
  have hf := circleFlux_sub_nonpos hχ hα hαη hr
  unfold circleFlux at hf
  simp_rw [normalComponent_circleMap hχ] at hf
  rw [setIntegral_const, setIntegral_const,
    Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])] at hf
  simp only [smul_eq_mul] at hf
  have hp : 0 < (Real.pi - -Real.pi) * r := mul_pos (by linarith [Real.pi_pos]) hr
  apply nonpos_of_mul_nonpos_left (b := (Real.pi - -Real.pi) * r) _ hp
  nlinarith only [hf]

/-- The two radial derivative bounds used at zero and infinity in Lemma 3.1. -/
theorem abs_radialComponent_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hα : 0 < α) {r : ℝ} (hr : 0 < r) :
    |⟪convolvedField χ 0 α (r : ℂ), (1 : ℂ)⟫| ≤
      min (Real.pi * M / α ^ 2 * r) r⁻¹ := by
  rw [radialComponent_convolvedField hχ hα hr, abs_div,
    abs_neg, abs_of_nonneg (massProfile_nonneg χ α r), abs_of_pos hr]
  apply le_min
  · apply (div_le_iff₀ hr).mpr
    nlinarith [massProfile_le_sq hχ hM hα hr.le]
  · simpa only [one_div] using div_le_div_of_nonneg_right (massProfile_le_one hχ hα r) hr.le

end MultipoleBKT.RouteFlux

end
