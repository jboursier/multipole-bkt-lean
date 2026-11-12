/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.RouteHessian.Radial
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Integration by parts for the radial Hessian on punctured domains

See Lemma 3.1 of the paper. Radial integration by parts uses absolute continuity of enclosed
mass. Angular integration by parts has cancelling endpoint values on the circle.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped RealInnerProductSpace

namespace MultipoleBKT.RouteHessian

open RouteFlux

variable {χ : ℂ → ℝ} {lam : ℝ}

/-- Radial integration by parts outside a disc. The measurable polar density
is the almost everywhere mass derivative, so no classical source derivative
is required. -/
theorem integral_massProfile_mul_radialDeriv (hχ : IsMollifier χ) (hlam : 0 < lam)
    {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) {ε R : ℝ} (hε : 0 ≤ ε) (hεR : ε ≤ R)
    (θ : ℝ) :
    (∫ r in ε..R, massProfile χ lam r *
      fderiv ℝ ξ (circleMap 0 r θ) (Complex.exp (θ * Complex.I))) =
      massProfile χ lam R * ξ (circleMap 0 R θ) -
        massProfile χ lam ε * ξ (circleMap 0 ε θ) -
          ∫ r in ε..R, massDensity χ lam r * ξ (circleMap 0 r θ) := by
  have hm := absolutelyContinuousOnInterval_massProfile hχ hlam hε hεR
  have hg := (TwoComponentCoulomb.contDiff_comp_circleMap_radius hξ θ).contDiffOn
    (s := uIcc ε R) |>.absolutelyContinuousOnInterval
  have he := hm.integral_mul_deriv_eq_deriv_mul hg
  have hleft : (fun r => massProfile χ lam r * deriv (fun s => ξ (circleMap 0 s θ)) r) =
      fun r => massProfile χ lam r *
        fderiv ℝ ξ (circleMap 0 r θ) (Complex.exp (θ * Complex.I)) := by
    funext r
    rw [(TwoComponentCoulomb.hasDerivAt_comp_circleMap_radius hξ θ r).deriv]
  rw [hleft] at he
  rw [he]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_hasDerivAt_massProfile hχ lam] with r hr hrmem
  rw [uIoc_of_le hεR] at hrmem
  rw [(hr (hε.trans_lt hrmem.1)).deriv]

/-- Resolution into radial and tangential directions in the plane. -/
theorem unit_decomposition {u : ℂ} (hu : ‖u‖ = 1) (v : ℂ) :
    ⟪u, v⟫ • u + ⟪Complex.I * u, v⟫ • (Complex.I * u) = v := by
  have hn : u.re ^ 2 + u.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, hu, sq] using Complex.normSq_eq_norm_sq u
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_sub, zero_add, Complex.inner,
      Complex.conj_re, Complex.conj_im, Complex.mul_re, smul_eq_mul]
  · linear_combination v.re * hn
  · linear_combination v.im * hn

/-- The Cartesian directional derivative splits into its radial and angular
parts on every positive-radius circle. -/
theorem radial_angular_decomposition {ξ : ℂ → ℝ} (r θ : ℝ) (v : ℂ) :
    fderiv ℝ ξ (circleMap 0 r θ) v =
      ⟪Complex.exp (θ * Complex.I), v⟫ *
        fderiv ℝ ξ (circleMap 0 r θ) (Complex.exp (θ * Complex.I)) +
      ⟪Complex.I * Complex.exp (θ * Complex.I), v⟫ *
        fderiv ℝ ξ (circleMap 0 r θ) (Complex.I * Complex.exp (θ * Complex.I)) := by
  conv_lhs => rw [← unit_decomposition (Complex.norm_exp_ofReal_mul_I θ) v]
  rw [map_add, map_smul, map_smul]
  rfl

private theorem unit_hasDerivAt (θ : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (t * Complex.I))
      (Complex.I * Complex.exp (θ * Complex.I)) θ := by
  have he : circleMap 0 1 = fun t : ℝ => Complex.exp (t * Complex.I) := by
    ext t
    simp [circleMap]
  have h := hasDerivAt_circleMap 0 1 θ
  rw [he] at h
  simpa only [mul_comm] using h

private theorem tangent_hasDerivAt (θ : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.I * Complex.exp (t * Complex.I))
      (-Complex.exp (θ * Complex.I)) θ := by
  convert (unit_hasDerivAt θ).const_mul Complex.I using 1
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]

/-- Angular integration by parts on a circle. Its endpoint terms cancel.
This is the angular part of the punctured-domain Hessian calculation. -/
theorem integral_angularDeriv_mul {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) (r : ℝ) (v w : ℂ) :
    (∫ θ in -Real.pi..Real.pi,
      fderiv ℝ ξ (circleMap 0 r θ) (circleMap 0 r θ * Complex.I) *
        (⟪Complex.exp (θ * Complex.I), w⟫ *
          ⟪Complex.I * Complex.exp (θ * Complex.I), v⟫)) =
      -(∫ θ in -Real.pi..Real.pi, ξ (circleMap 0 r θ) *
        (⟪Complex.I * Complex.exp (θ * Complex.I), w⟫ *
          ⟪Complex.I * Complex.exp (θ * Complex.I), v⟫ -
            ⟪Complex.exp (θ * Complex.I), w⟫ * ⟪Complex.exp (θ * Complex.I), v⟫)) := by
  let u : ℝ → ℂ := fun θ => Complex.exp (θ * Complex.I)
  let g : ℝ → ℝ := fun θ => ξ (circleMap 0 r θ)
  let a : ℝ → ℝ := fun θ => ⟪u θ, w⟫ * ⟪Complex.I * u θ, v⟫
  let g' : ℝ → ℝ := fun θ =>
    fderiv ℝ ξ (circleMap 0 r θ) (circleMap 0 r θ * Complex.I)
  let a' : ℝ → ℝ := fun θ => ⟪Complex.I * u θ, w⟫ * ⟪Complex.I * u θ, v⟫ -
    ⟪u θ, w⟫ * ⟪u θ, v⟫
  have hgd (θ : ℝ) : HasDerivAt g (g' θ) θ :=
    (hξ.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt θ
      (hasDerivAt_circleMap 0 r θ)
  have had (θ : ℝ) : HasDerivAt a (a' θ) θ := by
    have h1 := (unit_hasDerivAt θ).inner ℝ (hasDerivAt_const θ w)
    have h2 := (tangent_hasDerivAt θ).inner ℝ (hasDerivAt_const θ v)
    convert h1.mul h2 using 1
    simp only [inner_zero_right, zero_add, inner_neg_left, a', u]
    ring
  have hu : Continuous u := by dsimp [u]; fun_prop
  have hg : Continuous g := hξ.continuous.comp (continuous_circleMap 0 r)
  have ha : Continuous a := (hu.inner continuous_const).mul
    ((continuous_const.mul hu).inner continuous_const)
  have hg' : Continuous g' :=
    ((hξ.continuous_fderiv one_ne_zero).comp (continuous_circleMap 0 r)).clm_apply
      ((continuous_circleMap 0 r).mul continuous_const)
  have ha' : Continuous a' := by dsimp [a']; fun_prop
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := -Real.pi) (b := Real.pi) ha.continuousOn hg.continuousOn (fun θ _ => had θ) (fun θ _ => hgd θ)
    (ha'.intervalIntegrable _ _) (hg'.intervalIntegrable _ _)
  have he : a Real.pi * g Real.pi - a (-Real.pi) * g (-Real.pi) = 0 := by
    simp [g, a, u, circleMap, Complex.exp_pi_mul_I, Complex.exp_neg_pi_mul_I]
  rw [he, zero_sub] at hi
  simpa only [a, g, a', g', u, mul_comm] using hi

end MultipoleBKT.RouteHessian

end
