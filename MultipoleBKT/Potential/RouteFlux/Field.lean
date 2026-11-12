/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.RouteFlux.RadialFlux

/-!
# The radial convolution field

See Lemma 3.1 of the paper. Reflection symmetry removes the tangential component.
The radial component has already been recovered from flux. The mass bound
then gives the linear estimate at the origin used in the weak-Hessian argument.
Continuity from local integrability is proved earlier in `RouteFlux.Continuity`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace MultipoleBKT.RouteFlux

variable {χ : ℂ → ℝ} {α : ℝ}

private theorem map_conj_charge (hχ : IsMollifier χ) (α : ℝ) :
    (smearedCharge χ 0 α).map (starRingEnd ℂ) = smearedCharge χ 0 α := by
  rw [smearedCharge_eq_withDensity]
  refine map_withDensity_of_measurableEmbedding
    Complex.conjCLE.toHomeomorph.measurableEmbedding
    (LinearIsometryEquiv.measurePreserving Complex.conjLIE).map_eq
    (h := smearedDensity χ 0 α) fun x => ?_
  have he : χ ((starRingEnd ℂ x - 0) / (α : ℂ)) = χ ((x - 0) / (α : ℂ)) :=
    hχ.radial (by simp only [sub_zero, norm_div, Complex.norm_conj])
  change ENNReal.ofReal ((α ^ 2)⁻¹ * χ ((x - 0) / (α : ℂ))) =
    ENNReal.ofReal ((α ^ 2)⁻¹ * χ ((starRingEnd ℂ x - 0) / (α : ℂ)))
  rw [he]

private theorem pointField_conj (x : ℂ) :
    pointField (starRingEnd ℂ x) = starRingEnd ℂ (pointField x) := by
  simp [pointField, Complex.real_smul]

/-- Reflection covariance of the convolved point field. -/
theorem convolvedField_conj (hχ : IsMollifier χ) (α : ℝ) (x : ℂ) :
    convolvedField χ 0 α (starRingEnd ℂ x) = starRingEnd ℂ (convolvedField χ 0 α x) := by
  unfold convolvedField
  conv_lhs => rw [← map_conj_charge hχ α]
  have he : MeasurableEmbedding (starRingEnd ℂ) :=
    Complex.conjCLE.toHomeomorph.measurableEmbedding
  rw [he.integral_map]
  simp_rw [← map_sub, pointField_conj]
  rw [integral_conj]

/-- On the real radius the field is real, and flux identifies its value. -/
theorem convolvedField_ofReal (hχ : IsMollifier χ) (hα : 0 < α) {r : ℝ} (hr : 0 < r) :
    convolvedField χ 0 α (r : ℂ) = ((-massProfile χ α r / r : ℝ) : ℂ) := by
  have hc := convolvedField_conj hχ α (r : ℂ)
  have hi := congrArg Complex.im hc
  simp only [Complex.conj_ofReal, Complex.conj_im] at hi
  apply Complex.ext
  · simpa [Complex.inner] using radialComponent_convolvedField hχ hα hr
  · simp only [Complex.ofReal_im]
    linarith

private theorem convolvedField_zero (hχ : IsMollifier χ) (α : ℝ) :
    convolvedField χ 0 α 0 = 0 := by
  have h := convolvedField_mul_unit hχ α (u := -1) (by norm_num) 0
  simp only [mul_zero, neg_one_mul] at h
  exact self_eq_neg.mp h

/-- The radial field formula, recovered from flux and symmetries of the source.
It includes the origin without a differentiability assumption on the density. -/
theorem convolvedField_eq_massProfile (hχ : IsMollifier χ) (hα : 0 < α) (x : ℂ) :
    convolvedField χ 0 α x = -(massProfile χ α ‖x‖ / ‖x‖ ^ 2) • x := by
  by_cases hx : x = 0
  · subst x
    simp [convolvedField_zero hχ]
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let u : ℂ := x / (‖x‖ : ℂ)
  have hu : ‖u‖ = 1 := by
    simp [u, Complex.norm_real, hr.ne']
  have he : u * (‖x‖ : ℂ) = x := div_mul_cancel₀ x (Complex.ofReal_ne_zero.mpr hr.ne')
  calc
    convolvedField χ 0 α x = u * convolvedField χ 0 α (‖x‖ : ℂ) := by
      rw [← convolvedField_mul_unit hχ α hu, he]
    _ = u * ((-massProfile χ α ‖x‖ / ‖x‖ : ℝ) : ℂ) := by rw [convolvedField_ofReal hχ hα hr]
    _ = -(massProfile χ α ‖x‖ / ‖x‖ ^ 2) • x := by
      simp only [u, Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_div,
        Complex.ofReal_pow]
      field_simp

/-- The linear field bound at the origin, used when removing the puncture
in the weak-Hessian proof of Lemma 3.1. -/
theorem norm_convolvedField_le_mul (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hα : 0 < α) (x : ℂ) :
    ‖convolvedField χ 0 α x‖ ≤ Real.pi * M / α ^ 2 * ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    simp [convolvedField_zero hχ]
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [convolvedField_eq_massProfile hχ hα, norm_smul, Real.norm_eq_abs,
    abs_neg, abs_of_nonneg (div_nonneg (massProfile_nonneg χ α ‖x‖) (sq_nonneg _))]
  have hm := massProfile_le_sq hχ hM hα hr.le
  calc massProfile χ α ‖x‖ / ‖x‖ ^ 2 * ‖x‖ = massProfile χ α ‖x‖ / ‖x‖ := by field_simp
    _ ≤ Real.pi * M / α ^ 2 * ‖x‖ := by
      apply (div_le_iff₀ hr).mpr
      nlinarith

end MultipoleBKT.RouteFlux

end
