/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.RouteHessian.Integration
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TwoComponentCoulomb.Potential.Fundamental

/-!
# The weak Hessian across the origin

See Lemma 3.1 of the paper. Radial and angular integration by parts on a punctured disc
identify the weak Hessian. The inner circle term vanishes quadratically.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped RealInnerProductSpace

namespace MultipoleBKT.RouteHessian

open RouteFlux

variable {χ : ℂ → ℝ} {lam : ℝ}

private noncomputable def weakIntegrand (χ : ℂ → ℝ) (lam : ℝ) (ξ : ℂ → ℝ)
    (v w x : ℂ) : ℝ :=
  fderiv ℝ ξ x v * ⟪convolvedField χ 0 lam x, w⟫ +
    ξ x * ⟪radialHessian χ lam x v, w⟫

private theorem measurable_weakIntegrand (hχ : IsMollifier χ) (hlam : 0 < lam)
    {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) (v w : ℂ) :
    Measurable (weakIntegrand χ lam ξ v w) :=
  (((hξ.continuous_fderiv one_ne_zero).clm_apply continuous_const).measurable.mul
    ((continuous_convolvedField hχ hlam).inner continuous_const).measurable).add
      (hξ.continuous.measurable.mul
        (((measurable_radialHessian hχ).apply_continuousLinearMap v).inner_const))

private theorem locallyIntegrable_hessianComponent (hχ : IsMollifier χ)
    (hlam : 0 < lam) (v w : ℂ) :
    LocallyIntegrable (fun x => ⟪radialHessian χ lam x v, w⟫) volume := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  apply locallyIntegrable_iff.mpr
  intro K hK
  refine IntegrableOn.of_bound hK.measure_lt_top
    (((measurable_radialHessian hχ).apply_continuousLinearMap v).inner_const).aestronglyMeasurable
    (3 * (Real.pi * M / lam ^ 2) * ‖v‖ * ‖w‖) (Eventually.of_forall fun x => ?_)
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_radialHessian_le hχ hM hlam x) (norm_nonneg v)))
        (norm_nonneg w))

private theorem integrable_weakIntegrand (hχ : IsMollifier χ) (hlam : 0 < lam)
    {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ) (v w : ℂ) :
    Integrable (weakIntegrand χ lam ξ v w) := by
  have hg : Continuous (fun x => fderiv ℝ ξ x v * ⟪convolvedField χ 0 lam x, w⟫) :=
    ((hξ.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
      ((continuous_convolvedField hχ hlam).inner continuous_const)
  have hgc : HasCompactSupport (fun x => fderiv ℝ ξ x v * ⟪convolvedField χ 0 lam x, w⟫) :=
    by
    have hcv : HasCompactSupport (fun x => fderiv ℝ ξ x v) :=
      (hc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L v) rfl
    exact hcv.mul_right
  exact (hg.integrable_of_hasCompactSupport hgc).add
    ((locallyIntegrable_hessianComponent hχ hlam v w).integrable_smul_left_of_hasCompactSupport
      hξ.continuous hc)

private theorem polar_weakIntegrand (hχ : IsMollifier χ) (hlam : 0 < lam)
    (ξ : ℂ → ℝ) {r : ℝ} (hr : 0 < r) (θ : ℝ) (v w : ℂ) :
    r * weakIntegrand χ lam ξ v w (circleMap 0 r θ) =
      -(massProfile χ lam r *
          fderiv ℝ ξ (circleMap 0 r θ) (Complex.exp (θ * Complex.I)) +
        massDensity χ lam r * ξ (circleMap 0 r θ)) *
          (⟪Complex.exp (θ * Complex.I), w⟫ * ⟪Complex.exp (θ * Complex.I), v⟫) -
      massProfile χ lam r / r *
        (fderiv ℝ ξ (circleMap 0 r θ) (circleMap 0 r θ * Complex.I) *
            (⟪Complex.exp (θ * Complex.I), w⟫ *
              ⟪Complex.I * Complex.exp (θ * Complex.I), v⟫) +
          ξ (circleMap 0 r θ) *
            (⟪Complex.I * Complex.exp (θ * Complex.I), w⟫ *
                ⟪Complex.I * Complex.exp (θ * Complex.I), v⟫ -
              ⟪Complex.exp (θ * Complex.I), w⟫ * ⟪Complex.exp (θ * Complex.I), v⟫)) := by
  unfold weakIntegrand
  rw [convolvedField_circleMap hχ hlam hr, real_inner_smul_left,
    inner_radialHessian_circleMap hr, radial_angular_decomposition r θ v]
  have he : circleMap 0 r θ * Complex.I =
      r • (Complex.I * Complex.exp (θ * Complex.I)) := by
    simp [circleMap, Complex.real_smul, mul_comm, mul_left_comm]
  rw [he, map_smul]
  dsimp only [smul_eq_mul, tangentialCoefficient, densityCoefficient]
  field_simp
  ring

private noncomputable def angularRemainder (ξ : ℂ → ℝ) (v w : ℂ) (r θ : ℝ) : ℝ :=
  fderiv ℝ ξ (circleMap 0 r θ) (circleMap 0 r θ * Complex.I) *
      (⟪Complex.exp (θ * Complex.I), w⟫ * ⟪Complex.I * Complex.exp (θ * Complex.I), v⟫) +
    ξ (circleMap 0 r θ) *
      (⟪Complex.I * Complex.exp (θ * Complex.I), w⟫ *
          ⟪Complex.I * Complex.exp (θ * Complex.I), v⟫ -
        ⟪Complex.exp (θ * Complex.I), w⟫ * ⟪Complex.exp (θ * Complex.I), v⟫)

private theorem continuous_angularRemainder {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) (v w : ℂ) :
    Continuous (fun p : ℝ × ℝ => angularRemainder ξ v w p.1 p.2) := by
  have hp : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
    simp only [circleMap, zero_add]
    fun_prop
  have hf := ((hξ.continuous_fderiv one_ne_zero).comp hp).clm_apply
    (hp.mul (continuous_const (y := Complex.I)))
  have hg := hξ.continuous.comp hp
  unfold angularRemainder
  fun_prop

private theorem integral_angularRemainder {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ)
    (v w : ℂ) (r : ℝ) :
    (∫ θ in Ioo (-Real.pi) Real.pi, angularRemainder ξ v w r θ) = 0 := by
  have hp : Continuous (fun θ : ℝ => circleMap 0 r θ) := continuous_circleMap 0 r
  have hf := ((hξ.continuous_fderiv one_ne_zero).comp hp).clm_apply
    (hp.mul (continuous_const (y := Complex.I)))
  have hg := hξ.continuous.comp hp
  have hu : Continuous (fun θ : ℝ => Complex.exp (θ * Complex.I)) := by fun_prop
  have ha : Continuous (fun θ : ℝ => ⟪Complex.exp (θ * Complex.I), w⟫ *
      ⟪Complex.I * Complex.exp (θ * Complex.I), v⟫) := by fun_prop
  have hb : Continuous (fun θ : ℝ =>
      ⟪Complex.I * Complex.exp (θ * Complex.I), w⟫ *
        ⟪Complex.I * Complex.exp (θ * Complex.I), v⟫ -
      ⟪Complex.exp (θ * Complex.I), w⟫ * ⟪Complex.exp (θ * Complex.I), v⟫) := by fun_prop
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  unfold angularRemainder
  have hi1 := (hf.mul ha).intervalIntegrable (μ := volume) (-Real.pi) Real.pi
  have hi2 := (hg.mul hb).intervalIntegrable (μ := volume) (-Real.pi) Real.pi
  simp only [Pi.mul_def, Function.comp_def] at hi1 hi2
  rw [intervalIntegral.integral_add hi1 hi2, integral_angularDeriv_mul hξ]
  exact neg_add_cancel _

private theorem intervalIntegrable_massDensity (hχ : IsMollifier χ) (hlam : 0 < lam)
    {ε R : ℝ} (hε : 0 ≤ ε) (hεR : ε ≤ R) :
    IntervalIntegrable (massDensity χ lam) volume ε R := by
  have hm := absolutelyContinuousOnInterval_massProfile hχ hlam hε hεR
  apply hm.intervalIntegrable_deriv.congr_ae
  filter_upwards [ae_restrict_of_ae (ae_hasDerivAt_massProfile hχ lam),
    ae_restrict_mem measurableSet_uIoc] with r hr hmem
  rw [uIoc_of_le hεR] at hmem
  exact (hr (hε.trans_lt hmem.1)).deriv

private theorem integral_radialRemainder (hχ : IsMollifier χ) (hlam : 0 < lam)
    {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) {ε R : ℝ} (hε : 0 ≤ ε) (hεR : ε ≤ R)
    (θ : ℝ) (a : ℝ) :
    (∫ r in ε..R, -(massProfile χ lam r *
        fderiv ℝ ξ (circleMap 0 r θ) (Complex.exp (θ * Complex.I)) +
      massDensity χ lam r * ξ (circleMap 0 r θ)) * a) =
        -massProfile χ lam R * ξ (circleMap 0 R θ) * a +
          massProfile χ lam ε * ξ (circleMap 0 ε θ) * a := by
  have hm := absolutelyContinuousOnInterval_massProfile hχ hlam hε hεR
  have hd := intervalIntegrable_massDensity hχ hlam hε hεR
  have hg : Continuous (fun r : ℝ => ξ (circleMap 0 r θ)) :=
    (TwoComponentCoulomb.contDiff_comp_circleMap_radius hξ θ).continuous
  have hg' : Continuous (fun r : ℝ =>
      fderiv ℝ ξ (circleMap 0 r θ) (Complex.exp (θ * Complex.I))) :=
    ((hξ.continuous_fderiv one_ne_zero).comp (by
      simp only [circleMap, zero_add]
      fun_prop)).clm_apply continuous_const
  have hi1 : IntervalIntegrable (fun r => massProfile χ lam r *
      fderiv ℝ ξ (circleMap 0 r θ) (Complex.exp (θ * Complex.I))) volume ε R :=
    (hm.continuousOn.mul hg'.continuousOn).intervalIntegrable
  have hi2 : IntervalIntegrable (fun r => massDensity χ lam r * ξ (circleMap 0 r θ))
      volume ε R := hd.mul_continuousOn hg.continuousOn
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_neg,
    intervalIntegral.integral_add hi1 hi2,
    integral_massProfile_mul_radialDeriv hχ hlam hξ hε hεR]
  ring

private theorem polar_swap {f : ℝ × ℝ → ℝ} {ε R : ℝ} (hεR : ε ≤ R)
    (hf : ContinuousOn f (uIcc ε R ×ˢ Icc (-Real.pi) Real.pi)) :
    (∫ θ in Ioo (-Real.pi) Real.pi, ∫ r in ε..R, f (r, θ)) =
      ∫ r in ε..R, ∫ θ in Ioo (-Real.pi) Real.pi, f (r, θ) := by
  have hi := hf.integrableOn_compact (μ := (volume : Measure (ℝ × ℝ)))
    (isCompact_uIcc.prod isCompact_Icc)
  rw [uIcc_of_le hεR] at hi
  have hi' : Integrable (Function.uncurry (fun r θ => f (r, θ)))
      ((volume.restrict (Ioo ε R)).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact hi.mono_set (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  simp_rw [intervalIntegral.integral_of_le hεR, integral_Ioc_eq_integral_Ioo]
  exact (integral_integral_swap hi').symm

private theorem integral_polar_weakIntegrand (hχ : IsMollifier χ) (hlam : 0 < lam)
    {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R)
    (θ : ℝ) (v w : ℂ) :
    (∫ r in ε..R, r * weakIntegrand χ lam ξ v w (circleMap 0 r θ)) =
      (-massProfile χ lam R * ξ (circleMap 0 R θ) *
          (⟪Complex.exp (θ * Complex.I), w⟫ * ⟪Complex.exp (θ * Complex.I), v⟫) +
        massProfile χ lam ε * ξ (circleMap 0 ε θ) *
          (⟪Complex.exp (θ * Complex.I), w⟫ * ⟪Complex.exp (θ * Complex.I), v⟫)) -
      ∫ r in ε..R, massProfile χ lam r / r * angularRemainder ξ v w r θ := by
  have hm := absolutelyContinuousOnInterval_massProfile hχ hlam hε.le hεR
  have hne : ∀ r ∈ uIcc ε R, r ≠ 0 := by
    rw [uIcc_of_le hεR]
    exact fun r hr => ne_of_gt (hε.trans_le hr.1)
  have hmdiv := hm.continuousOn.div continuousOn_id hne
  have hg : Continuous (fun r : ℝ => ξ (circleMap 0 r θ)) :=
    (TwoComponentCoulomb.contDiff_comp_circleMap_radius hξ θ).continuous
  have hg' : Continuous (fun r : ℝ =>
      fderiv ℝ ξ (circleMap 0 r θ) (Complex.exp (θ * Complex.I))) :=
    ((hξ.continuous_fderiv one_ne_zero).comp (by
      simp only [circleMap, zero_add]
      fun_prop)).clm_apply continuous_const
  have hi1 : IntervalIntegrable (fun r => -(massProfile χ lam r *
      fderiv ℝ ξ (circleMap 0 r θ) (Complex.exp (θ * Complex.I)) +
      massDensity χ lam r * ξ (circleMap 0 r θ)) *
        (⟪Complex.exp (θ * Complex.I), w⟫ * ⟪Complex.exp (θ * Complex.I), v⟫)) volume ε R :=
    (((hm.continuousOn.mul hg'.continuousOn).intervalIntegrable.add
      ((intervalIntegrable_massDensity hχ hlam hε.le hεR).mul_continuousOn hg.continuousOn)).neg).mul_const _
  have ha : Continuous (fun r : ℝ => angularRemainder ξ v w r θ) :=
    (continuous_angularRemainder hξ v w).comp (continuous_id.prodMk continuous_const)
  have hi2 : IntervalIntegrable (fun r => massProfile χ lam r / r *
      angularRemainder ξ v w r θ) volume ε R :=
    (hmdiv.mul ha.continuousOn).intervalIntegrable
  calc
    _ = ∫ r in ε..R, -(massProfile χ lam r *
        fderiv ℝ ξ (circleMap 0 r θ) (Complex.exp (θ * Complex.I)) +
        massDensity χ lam r * ξ (circleMap 0 r θ)) *
          (⟪Complex.exp (θ * Complex.I), w⟫ * ⟪Complex.exp (θ * Complex.I), v⟫) -
        massProfile χ lam r / r * angularRemainder ξ v w r θ := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le hεR] at hr
      exact polar_weakIntegrand hχ hlam ξ (hε.trans_le hr.1) θ v w
    _ = _ := by
      rw [intervalIntegral.integral_sub hi1 hi2,
        integral_radialRemainder hχ hlam hξ hε.le hεR]

private theorem boundary_polar (hχ : IsMollifier χ) (hlam : 0 < lam)
    (ξ : ℂ → ℝ) (v w : ℂ) {r : ℝ} (hr : 0 < r) :
    originBoundary χ lam ξ v w r = ∫ θ in Ioo (-Real.pi) Real.pi,
      -massProfile χ lam r * ξ (circleMap 0 r θ) *
        (⟪Complex.exp (θ * Complex.I), w⟫ * ⟪Complex.exp (θ * Complex.I), v⟫) := by
  unfold originBoundary
  apply integral_congr_ae
  filter_upwards with θ
  rw [convolvedField_circleMap hχ hlam hr, real_inner_smul_left]
  have he : circleMap 0 r θ = r • Complex.exp (θ * Complex.I) := by
    simp [circleMap, Complex.real_smul]
  rw [he, real_inner_smul_left]
  field_simp

/-- Integration by parts on an annulus, with both circle boundary terms.
This is the punctured-domain calculation in Lemma 3.1. -/
theorem integral_annulus_hessian (hχ : IsMollifier χ) (hlam : 0 < lam)
    {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ)
    {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) (v w : ℂ) :
    (∫ x in ball (0 : ℂ) R \ closedBall 0 ε,
      fderiv ℝ ξ x v * ⟪convolvedField χ 0 lam x, w⟫ +
        ξ x * ⟪radialHessian χ lam x v, w⟫) =
      originBoundary χ lam ξ v w R - originBoundary χ lam ξ v w ε := by
  have hm := absolutelyContinuousOnInterval_massProfile hχ hlam hε.le hεR
  let A : ℝ × ℝ → ℝ := fun p =>
    massProfile χ lam p.1 / p.1 * angularRemainder ξ v w p.1 p.2
  have hA : ContinuousOn A (uIcc ε R ×ˢ Icc (-Real.pi) Real.pi) := by
    have hmc : ContinuousOn (fun p : ℝ × ℝ => massProfile χ lam p.1)
        (uIcc ε R ×ˢ Icc (-Real.pi) Real.pi) :=
      hm.continuousOn.comp continuous_fst.continuousOn (fun _ hp => hp.1)
    apply (hmc.div continuous_fst.continuousOn ?_).mul
      (continuous_angularRemainder hξ v w).continuousOn
    intro p hp
    have hp' := hp.1
    rw [uIcc_of_le hεR] at hp'
    exact ne_of_gt (hε.trans_le hp'.1)
  have hAi := hA.integrableOn_compact (μ := (volume : Measure (ℝ × ℝ)))
    (isCompact_uIcc.prod isCompact_Icc)
  rw [uIcc_of_le hεR] at hAi
  have hAi' : Integrable A
      ((volume.restrict (Ioo ε R)).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact hAi.mono_set (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hinner : IntegrableOn (fun θ => ∫ r in ε..R, A (r, θ))
      (Ioo (-Real.pi) Real.pi) := by
    simp_rw [intervalIntegral.integral_of_le hεR, integral_Ioc_eq_integral_Ioo]
    exact hAi'.integral_prod_right
  have hzero : (∫ θ in Ioo (-Real.pi) Real.pi, ∫ r in ε..R, A (r, θ)) = 0 := by
    rw [polar_swap hεR hA]
    simp only [A, integral_const_mul, integral_angularRemainder hξ, mul_zero,
      intervalIntegral.integral_zero]
  have hb (r : ℝ) : IntegrableOn (fun θ : ℝ =>
      -massProfile χ lam r * ξ (circleMap 0 r θ) *
        (⟪Complex.exp (θ * Complex.I), w⟫ * ⟪Complex.exp (θ * Complex.I), v⟫))
      (Ioo (-Real.pi) Real.pi) := by
    have hh : Continuous (fun θ : ℝ =>
        -massProfile χ lam r * ξ (circleMap 0 r θ) *
          (⟪Complex.exp (θ * Complex.I), w⟫ * ⟪Complex.exp (θ * Complex.I), v⟫)) := by
      have hg := hξ.continuous.comp (continuous_circleMap 0 r)
      fun_prop
    exact hh.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  change (∫ x in ball (0 : ℂ) R \ closedBall 0 ε, weakIntegrand χ lam ξ v w x) = _
  rw [integral_annulus_polar (measurable_weakIntegrand hχ hlam hξ v w) hε.le hεR
    (integrable_weakIntegrand hχ hlam hξ hc v w).integrableOn]
  simp_rw [integral_polar_weakIntegrand hχ hlam hξ hε hεR]
  have he (θ : ℝ) :
      -massProfile χ lam R * ξ (circleMap 0 R θ) *
          (⟪Complex.exp (θ * Complex.I), w⟫ * ⟪Complex.exp (θ * Complex.I), v⟫) +
        massProfile χ lam ε * ξ (circleMap 0 ε θ) *
          (⟪Complex.exp (θ * Complex.I), w⟫ * ⟪Complex.exp (θ * Complex.I), v⟫) =
      -massProfile χ lam R * ξ (circleMap 0 R θ) *
          (⟪Complex.exp (θ * Complex.I), w⟫ * ⟪Complex.exp (θ * Complex.I), v⟫) -
        (-massProfile χ lam ε * ξ (circleMap 0 ε θ) *
          (⟪Complex.exp (θ * Complex.I), w⟫ * ⟪Complex.exp (θ * Complex.I), v⟫)) := by
    ring
  simp_rw [he]
  have hbsub := (hb R).sub (hb ε)
  simp only [Pi.sub_def] at hbsub
  dsimp only [A] at hinner hzero
  rw [integral_sub hbsub hinner, hzero, sub_zero,
    integral_sub (hb R) (hb ε), boundary_polar hχ hlam ξ v w (hε.trans_le hεR),
    boundary_polar hχ hlam ξ v w hε]

private theorem tendsto_integral_annulus {F : ℂ → ℝ} {R : ℝ}
    (hi : IntegrableOn F (ball (0 : ℂ) R)) :
    Tendsto (fun ε : ℝ => ∫ x in ball (0 : ℂ) R \ closedBall 0 ε, F x)
      (𝓝[>] 0) (𝓝 (∫ x in ball (0 : ℂ) R, F x)) := by
  have he (ε : ℝ) : (∫ x in ball (0 : ℂ) R \ closedBall 0 ε, F x) =
      ∫ x in ball (0 : ℂ) R, (closedBall (0 : ℂ) ε)ᶜ.indicator F x := by
    rw [setIntegral_indicator measurableSet_closedBall.compl]
    rfl
  simp_rw [he]
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖F x‖)
  · exact Eventually.of_forall fun ε =>
      hi.aestronglyMeasurable.indicator measurableSet_closedBall.compl
  · exact Eventually.of_forall fun ε => Eventually.of_forall fun x => norm_indicator_le_norm_self _ _
  · exact hi.norm
  · have hn : ∀ᵐ x : ℂ, x ≠ 0 := by simp [ae_iff]
    filter_upwards [ae_restrict_of_ae hn] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_lt_nhds (norm_pos_iff.mpr hx)).filter_mono nhdsWithin_le_nhds]
      with ε hε
    exact (indicator_of_mem (show x ∈ (closedBall (0 : ℂ) ε)ᶜ by
      simpa only [mem_compl_iff, mem_closedBall_zero_iff, not_le] using hε) F).symm

/-- The radial tensor is the weak Hessian, with no distribution supported at zero.
The test is any compactly supported `C¹` function, and the directions are arbitrary.
The paper: Lemma 3.1. -/
theorem weakHessian_convolvedField (hχ : IsMollifier χ) (hlam : 0 < lam)
    {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ) (v w : ℂ) :
    (∫ x, fderiv ℝ ξ x v * ⟪convolvedField χ 0 lam x, w⟫) =
      -(∫ x, ξ x * ⟪radialHessian χ lam x v, w⟫) := by
  have hcv : HasCompactSupport (fun x => fderiv ℝ ξ x v) :=
    (hc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L v) rfl
  have hcW : HasCompactSupport (weakIntegrand χ lam ξ v w) :=
    hcv.mul_right.add hc.mul_right
  obtain ⟨R₁, hR₁, hξR⟩ := hc.exists_pos_le_norm
  obtain ⟨R₂, hR₂, hWR⟩ := hcW.exists_pos_le_norm
  let R := max R₁ R₂
  have hR : 0 < R := hR₁.trans_le (le_max_left _ _)
  have hboundary : originBoundary χ lam ξ v w R = 0 := by
    unfold originBoundary
    apply integral_eq_zero_of_ae
    filter_upwards with θ
    rw [hξR _ (by rw [norm_circleMap_zero, abs_of_pos hR]; exact le_max_left _ _)]
    simp
  have ht := tendsto_integral_annulus
    (R := R) (integrable_weakIntegrand hχ hlam hξ hc v w).integrableOn
  have ht' : Tendsto (fun ε : ℝ => ∫ x in ball (0 : ℂ) R \ closedBall 0 ε,
      weakIntegrand χ lam ξ v w x) (𝓝[>] 0) (𝓝 0) := by
    have hb := (tendsto_originBoundary_zero hχ hlam hξ.continuous hc v w).neg
    rw [neg_zero] at hb
    apply hb.congr'
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds] with ε hε hεR
    have he := integral_annulus_hessian hχ hlam hξ hc hε hεR.le v w
    rw [hboundary, zero_sub] at he
    exact he.symm
  have hz : (∫ x, weakIntegrand χ lam ξ v w x) = 0 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball (0 : ℂ) R) (fun x hx =>
      hWR x ((show R₂ ≤ R from le_max_right R₁ R₂).trans (show R ≤ ‖x‖ by simpa using hx)))]
    exact tendsto_nhds_unique ht ht'
  have hg : Continuous (fun x => fderiv ℝ ξ x v * ⟪convolvedField χ 0 lam x, w⟫) :=
    ((hξ.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
      ((continuous_convolvedField hχ hlam).inner continuous_const)
  have hi1 := hg.integrable_of_hasCompactSupport (μ := volume) hcv.mul_right
  have hi2 := (locallyIntegrable_hessianComponent hχ hlam v w).integrable_smul_left_of_hasCompactSupport
    hξ.continuous hc
  change (∫ x, fderiv ℝ ξ x v * ⟪convolvedField χ 0 lam x, w⟫ +
    ξ x * ⟪radialHessian χ lam x v, w⟫) = 0 at hz
  change Integrable (fun x => ξ x * ⟪radialHessian χ lam x v, w⟫) volume at hi2
  rw [integral_add hi1 hi2] at hz
  linarith

end MultipoleBKT.RouteHessian

end
