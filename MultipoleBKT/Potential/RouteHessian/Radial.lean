/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.RouteFlux.Potential
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Radial second derivatives and the bounded radial Hessian formula

See Lemma 3.1 of the paper. Differentiate the flux identity at the almost every radius
where enclosed mass has its polar derivative. The two eigenvalues of the
radial Hessian are controlled by the quadratic mass and density bounds.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped RealInnerProductSpace

namespace MultipoleBKT.RouteHessian

open RouteFlux

variable {χ : ℂ → ℝ} {lam : ℝ}

/-- The tangential coefficient in the radial Hessian formula. -/
noncomputable def tangentialCoefficient (χ : ℂ → ℝ) (lam r : ℝ) : ℝ :=
  massProfile χ lam r / r ^ 2

/-- Enclosed mass derivative divided by radius in the radial Hessian formula. -/
noncomputable def densityCoefficient (χ : ℂ → ℝ) (lam r : ℝ) : ℝ :=
  massDensity χ lam r / r

/-- The radial Hessian formula, expressed as a real linear operator.
Inverse-zero arithmetic extends the polar expression to zero. -/
noncomputable def radialHessian (χ : ℂ → ℝ) (lam : ℝ) (x : ℂ) : ℂ →L[ℝ] ℂ :=
  -(tangentialCoefficient χ lam ‖x‖) • ContinuousLinearMap.id ℝ ℂ +
    (2 * tangentialCoefficient χ lam ‖x‖ - densityCoefficient χ lam ‖x‖) •
      (innerSL ℝ (‖x‖⁻¹ • x)).smulRight (‖x‖⁻¹ • x)

/-- The quadratic enclosed mass estimate controls the tangential eigenvalue. -/
theorem tangentialCoefficient_mem_Icc (hχ : IsMollifier χ) {M : ℝ}
    (hM : ∀ x, χ x ≤ M) (hlam : 0 < lam) {r : ℝ} (hr : 0 ≤ r) :
    tangentialCoefficient χ lam r ∈ Icc 0 (Real.pi * M / lam ^ 2) := by
  have hM0 := hχ.nonneg_of_le hM
  refine ⟨div_nonneg (massProfile_nonneg χ lam r) (sq_nonneg r), ?_⟩
  rcases hr.eq_or_lt with rfl | hr
  · simp [tangentialCoefficient, show 0 ≤ Real.pi * M / lam ^ 2 by positivity]
  · exact (div_le_iff₀ (sq_pos_of_pos hr)).mpr (massProfile_le_sq hχ hM hlam hr.le)

/-- The polar density estimate controls the second coefficient. -/
theorem densityCoefficient_mem_Icc (hχ : IsMollifier χ) {M : ℝ}
    (hM : ∀ x, χ x ≤ M) {r : ℝ} (hr : 0 ≤ r) :
    densityCoefficient χ lam r ∈ Icc 0 (2 * (Real.pi * M / lam ^ 2)) := by
  have hM0 := hχ.nonneg_of_le hM
  rcases hr.eq_or_lt with rfl | hr
  · simp [densityCoefficient, show 0 ≤ 2 * (Real.pi * M / lam ^ 2) by positivity]
  · have he : densityCoefficient χ lam r = 2 * Real.pi * density χ lam (r : ℂ) := by
      unfold densityCoefficient massDensity
      field_simp
    rw [he]
    refine ⟨mul_nonneg (by positivity) (mul_nonneg (by positivity) (hχ.nonneg _)), ?_⟩
    dsimp [density]
    calc 2 * Real.pi * ((lam ^ 2)⁻¹ * χ ((r : ℂ) / (lam : ℂ))) ≤
        2 * Real.pi * ((lam ^ 2)⁻¹ * M) := by gcongr; exact hM _
      _ = 2 * (Real.pi * M / lam ^ 2) := by ring

/-- The radial eigenvalue has absolute value at most twice the mass bound. -/
theorem abs_radialCoefficient_le (hχ : IsMollifier χ) {M : ℝ}
    (hM : ∀ x, χ x ≤ M) (hlam : 0 < lam) {r : ℝ} (hr : 0 ≤ r) :
    |tangentialCoefficient χ lam r - densityCoefficient χ lam r| ≤
      2 * (Real.pi * M / lam ^ 2) := by
  have ha := tangentialCoefficient_mem_Icc hχ hM hlam hr
  have hb := densityCoefficient_mem_Icc hχ hM hr (lam := lam)
  rw [abs_le]
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

/-- Operator bound for the radial Hessian formula, including the origin. -/
theorem norm_radialHessian_le (hχ : IsMollifier χ) {M : ℝ}
    (hM : ∀ x, χ x ≤ M) (hlam : 0 < lam) (x : ℂ) :
    ‖radialHessian χ lam x‖ ≤ 3 * (Real.pi * M / lam ^ 2) := by
  have hM0 := hχ.nonneg_of_le hM
  have hK : 0 ≤ Real.pi * M / lam ^ 2 := by positivity
  have ha := tangentialCoefficient_mem_Icc hχ hM hlam (norm_nonneg x)
  have hb := densityCoefficient_mem_Icc hχ hM (norm_nonneg x) (lam := lam)
  have hc : |2 * tangentialCoefficient χ lam ‖x‖ - densityCoefficient χ lam ‖x‖| ≤
      2 * (Real.pi * M / lam ^ 2) := by
    rw [abs_le]
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  have hu : ‖‖x‖⁻¹ • x‖ ≤ 1 := by
    by_cases hx : x = 0
    · simp [hx]
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  have hp : ‖(innerSL ℝ (‖x‖⁻¹ • x)).smulRight (‖x‖⁻¹ • x)‖ ≤ 1 := by
    rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
    nlinarith [norm_nonneg (‖x‖⁻¹ • x)]
  unfold radialHessian
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg ha.1, ContinuousLinearMap.norm_id, mul_one]
  have hh := mul_le_mul hc hp (norm_nonneg _) (by positivity : 0 ≤ 2 * (Real.pi * M / lam ^ 2))
  nlinarith [ha.2]

/-- The flux identity differentiated at almost every radius.
No continuity of the source density is assumed. -/
theorem ae_hasDerivAt_radialGradient (hχ : IsMollifier χ) (hlam : 0 < lam) :
    ∀ᵐ r : ℝ, 0 < r →
      HasDerivAt (fun t : ℝ => deriv (fun s : ℝ => smearedPotential χ lam (s : ℂ)) t)
        (tangentialCoefficient χ lam r - densityCoefficient χ lam r) r := by
  filter_upwards [ae_hasDerivAt_massProfile hχ lam] with r hr hr0
  have hd := ((hr hr0).neg.div (hasDerivAt_id r) hr0.ne')
  have he : (-massDensity χ lam r * r - -massProfile χ lam r * 1) / r ^ 2 =
      tangentialCoefficient χ lam r - densityCoefficient χ lam r := by
    unfold tangentialCoefficient densityCoefficient
    field_simp
    ring
  dsimp only [id_eq, Pi.neg_apply] at hd
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hr0] with t ht
  exact (hasDerivAt_smearedPotential_radial hχ hlam ht).deriv

/-- The almost everywhere radial second-derivative estimate in Lemma 3.1.
Together with the tangential term this is the bound used for the Hessian. -/
theorem ae_abs_radialSecondDeriv_add_le (hχ : IsMollifier χ) {M : ℝ}
    (hM : ∀ x, χ x ≤ M) (hlam : 0 < lam) :
    ∀ᵐ r : ℝ, 0 < r →
      |deriv (deriv (fun s : ℝ => smearedPotential χ lam (s : ℂ))) r| +
        |deriv (fun s : ℝ => smearedPotential χ lam (s : ℂ)) r| / r ≤
          3 * (Real.pi * M / lam ^ 2) := by
  filter_upwards [ae_hasDerivAt_radialGradient hχ hlam] with r hr hr0
  rw [(hr hr0).deriv, (hasDerivAt_smearedPotential_radial hχ hlam hr0).deriv]
  have ha := tangentialCoefficient_mem_Icc hχ hM hlam hr0.le
  have hb := abs_radialCoefficient_le hχ hM hlam hr0.le
  have he : |-massProfile χ lam r / r| / r = tangentialCoefficient χ lam r := by
    rw [abs_div, abs_neg, abs_of_nonneg (massProfile_nonneg χ lam r), abs_of_pos hr0]
    unfold tangentialCoefficient
    ring
  rw [he]
  linarith [ha.2]

end MultipoleBKT.RouteHessian

end
