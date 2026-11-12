/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.RouteHessian.Annular
public import MultipoleBKT.Potential.RouteHessian.Origin

/-!
# Polar form of the radial Hessian

See Lemma 3.1 of the paper. The radial and tangential eigenvalues give the polar integrand
used in integration by parts on an annulus.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped RealInnerProductSpace

namespace MultipoleBKT.RouteHessian

open RouteFlux

variable {χ : ℂ → ℝ} {lam : ℝ}

private theorem circleMap_eq_smul (r θ : ℝ) :
    circleMap 0 r θ = r • Complex.exp (θ * Complex.I) := by
  simp [circleMap, Complex.real_smul]

/-- The field expressed in polar coordinates, with its coefficient recovered
from Poisson flux. -/
theorem convolvedField_circleMap (hχ : IsMollifier χ) (hlam : 0 < lam)
    {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    convolvedField χ 0 lam (circleMap 0 r θ) =
      (-massProfile χ lam r / r) • Complex.exp (θ * Complex.I) := by
  rw [convolvedField_eq_massProfile hχ hlam, norm_circleMap_zero, abs_of_pos hr,
    circleMap_eq_smul, smul_smul]
  congr 1
  field_simp

/-- Radial and tangential eigenvalues of the Hessian formula on a circle. -/
theorem inner_radialHessian_circleMap {r : ℝ} (hr : 0 < r) (θ : ℝ) (v w : ℂ) :
    ⟪radialHessian χ lam (circleMap 0 r θ) v, w⟫ =
      (tangentialCoefficient χ lam r - densityCoefficient χ lam r) *
        (⟪Complex.exp (θ * Complex.I), v⟫ * ⟪Complex.exp (θ * Complex.I), w⟫) -
      tangentialCoefficient χ lam r *
        (⟪Complex.I * Complex.exp (θ * Complex.I), v⟫ *
          ⟪Complex.I * Complex.exp (θ * Complex.I), w⟫) := by
  have hu : ‖circleMap 0 r θ‖⁻¹ • circleMap 0 r θ = Complex.exp (θ * Complex.I) := by
    rw [norm_circleMap_zero, abs_of_pos hr, circleMap_eq_smul, smul_smul,
      inv_mul_cancel₀ hr.ne', one_smul]
  have hvw : ⟪v, w⟫ =
      ⟪Complex.exp (θ * Complex.I), v⟫ * ⟪Complex.exp (θ * Complex.I), w⟫ +
        ⟪Complex.I * Complex.exp (θ * Complex.I), v⟫ *
          ⟪Complex.I * Complex.exp (θ * Complex.I), w⟫ := by
    conv_lhs => rw [← unit_decomposition (Complex.norm_exp_ofReal_mul_I θ) v]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  unfold radialHessian
  rw [hu]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    real_inner_smul_left, inner_add_left, norm_circleMap_zero, abs_of_pos hr]
  rw [hvw]
  ring

end MultipoleBKT.RouteHessian

end
