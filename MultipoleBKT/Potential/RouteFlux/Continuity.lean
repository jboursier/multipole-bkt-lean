/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.RouteFlux.WeakPoisson
import TwoComponentCoulomb.Potential.DiscField
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Continuity from the locally integrable fundamental field

See Lemma 3.1 of the paper.
Cutting off the singularity gives continuous convolution fields. Their uniform
error is bounded by the local integral of `|x|⁻¹`, which is `2π ε` on a disc of
radius `ε`. This proves continuity before invoking the radial flux formula.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace MultipoleBKT.RouteFlux

variable {χ : ℂ → ℝ} {α : ℝ}

private noncomputable def cutoffField (ε : ℝ) (x : ℂ) : ℂ :=
  -((max ‖x‖ ε) ^ 2)⁻¹ • x

private theorem continuous_cutoffField {ε : ℝ} (hε : 0 < ε) : Continuous (cutoffField ε) := by
  have hp (x : ℂ) : max ‖x‖ ε ≠ 0 := ne_of_gt (hε.trans_le (le_max_right _ _))
  exact (((continuous_norm.max continuous_const).pow 2).inv₀
    (fun x => pow_ne_zero 2 (hp x))).neg.smul continuous_id

private theorem norm_cutoffField_le {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    ‖cutoffField ε x‖ ≤ ε⁻¹ := by
  rw [cutoffField, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  have hm : 0 < max ‖x‖ ε := hε.trans_le (le_max_right _ _)
  calc
    (max ‖x‖ ε ^ 2)⁻¹ * ‖x‖ ≤ (max ‖x‖ ε ^ 2)⁻¹ * max ‖x‖ ε := by
      gcongr
      exact le_max_left _ _
    _ = (max ‖x‖ ε)⁻¹ := by field_simp
    _ ≤ ε⁻¹ := inv_anti₀ hε (le_max_right _ _)

private theorem norm_cutoffField_le_pointField (ε : ℝ) (x : ℂ) :
    ‖cutoffField ε x‖ ≤ ‖pointField x‖ := by
  by_cases hx : x = 0
  · simp [hx, cutoffField, pointField]
  have hr := norm_pos_iff.mpr hx
  rw [cutoffField, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _)), pointField,
    TwoComponentCoulomb.norm_gradLogKernel]
  calc
    (max ‖x‖ ε ^ 2)⁻¹ * ‖x‖ ≤ (‖x‖ ^ 2)⁻¹ * ‖x‖ := by
      gcongr
      exact le_max_left _ _
    _ = ‖x‖⁻¹ := by field_simp

private theorem cutoffField_eq_of_le {ε : ℝ} {x : ℂ} (hx : ε ≤ ‖x‖) :
    cutoffField ε x = pointField x := by simp only [cutoffField, pointField, max_eq_left hx]

private theorem integral_norm_pointField_ball {ε : ℝ} (hε : 0 < ε) :
    ∫ x in ball (0 : ℂ) ε, ‖pointField x‖ = 2 * Real.pi * ε := by
  simp_rw [pointField, TwoComponentCoulomb.norm_gradLogKernel]
  rw [TwoComponentCoulomb.setIntegral_ball_zero_eq_polar_of_measurable
    (F := fun x : ℂ => ‖x‖⁻¹) measurable_norm.inv (TwoComponentCoulomb.integrableOn_inv_norm_ball_zero ε)]
  have he : ∀ r ∈ Ioo (0 : ℝ) ε,
      r • (∫ θ in Ioo (-Real.pi) Real.pi, ‖circleMap 0 r θ‖⁻¹) = 2 * Real.pi := by
    intro r hr
    simp_rw [norm_circleMap_zero, abs_of_pos hr.1]
    rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
    simp only [smul_eq_mul]
    field_simp [hr.1.ne']
    ring
  rw [setIntegral_congr_fun measurableSet_Ioo he, setIntegral_const,
    Real.volume_real_Ioo_of_le hε.le, smul_eq_mul]
  ring

private theorem integral_local_pointField_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    ∫ y in ball x ε, ‖pointField (x - y)‖ ∂smearedCharge χ 0 α ≤
      (M / α ^ 2) * (2 * Real.pi * ε) := by
  have hM0 := hχ.nonneg_of_le hM
  have hle : smearedCharge χ 0 α ≤ ENNReal.ofReal (M / α ^ 2) • (volume : Measure ℂ) := by
    refine (smearedCharge_le_smul_restrict hχ hM hα).trans fun s => ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_right (Measure.restrict_apply_le _ _) _
  have hi : IntegrableOn (fun y : ℂ => ‖pointField (x - y)‖) (ball x ε) :=
    (TwoComponentCoulomb.integrableOn_comp_sub_ball
      TwoComponentCoulomb.integrableOn_gradLogKernel_ball_zero x x ε).norm
  have h : ∫ y in ball x ε, ‖pointField (x - y)‖ ∂smearedCharge χ 0 α ≤
      ∫ y, ‖pointField (x - y)‖ ∂(ENNReal.ofReal (M / α ^ 2) • volume.restrict (ball x ε)) := by
    apply integral_mono_measure
      (show (smearedCharge χ 0 α).restrict (ball x ε) ≤
        ENNReal.ofReal (M / α ^ 2) • volume.restrict (ball x ε) by
          rw [← Measure.restrict_smul]
          exact Measure.restrict_mono le_rfl hle)
      (Eventually.of_forall fun _ => norm_nonneg _)
      (hi.smul_measure ENNReal.ofReal_ne_top)
  refine h.trans (le_of_eq ?_)
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul,
    TwoComponentCoulomb.setIntegral_ball_eq_setIntegral_ball_zero_of_vec]
  have he : ∀ y : ℂ, ‖pointField (x - (x + y))‖ = ‖pointField y‖ := by
    intro y
    simp [pointField]
  simp_rw [he]
  rw [integral_norm_pointField_ball hε]

private noncomputable def cutoffConvolution (χ : ℂ → ℝ) (α ε : ℝ) (x : ℂ) : ℂ :=
  ∫ y, cutoffField ε (x - y) ∂smearedCharge χ 0 α

private theorem continuous_cutoffConvolution (hχ : IsMollifier χ) (α : ℝ)
    {ε : ℝ} (hε : 0 < ε) : Continuous (cutoffConvolution χ α ε) := by
  have := isFiniteMeasure_smearedCharge hχ 0 α
  apply continuous_iff_continuousAt.mpr
  intro x
  apply continuousAt_of_dominated (bound := fun _ => ε⁻¹)
    (Eventually.of_forall fun z => ((continuous_cutoffField hε).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall fun z => Eventually.of_forall fun y => norm_cutoffField_le hε (z - y))
    (integrable_const _)
    (Eventually.of_forall fun y => ((continuous_cutoffField hε).comp
      (continuous_id.sub continuous_const)).continuousAt)

private theorem norm_cutoffConvolution_sub_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    ‖cutoffConvolution χ α ε x - convolvedField χ 0 α x‖ ≤
      4 * Real.pi * (M / α ^ 2) * ε := by
  have := isFiniteMeasure_smearedCharge hχ 0 α
  have hc : Integrable (fun y => cutoffField ε (x - y)) (smearedCharge χ 0 α) :=
    Integrable.of_bound ((continuous_cutoffField hε).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable ε⁻¹
      (Eventually.of_forall fun y => norm_cutoffField_le hε _)
  have hi := integrable_gradLogKernel_sub_smearedCharge hχ x 0 hα
  have hb : ∀ y : ℂ, ‖cutoffField ε (x - y) - pointField (x - y)‖ ≤
      2 * (ball x ε).indicator (fun y => ‖pointField (x - y)‖) y := by
    intro y
    by_cases hy : y ∈ ball x ε
    · rw [indicator_of_mem hy]
      exact (norm_sub_le _ _).trans (by linarith [norm_cutoffField_le_pointField ε (x - y)])
    · rw [indicator_of_notMem hy, cutoffField_eq_of_le (by
        simpa only [mem_ball, dist_eq_norm, norm_sub_rev, not_lt] using hy), sub_self, norm_zero]
      simp
  rw [cutoffConvolution, convolvedField, ← integral_sub hc hi]
  calc ‖∫ y, cutoffField ε (x - y) - pointField (x - y) ∂smearedCharge χ 0 α‖ ≤
      ∫ y, 2 * (ball x ε).indicator (fun y => ‖pointField (x - y)‖) y ∂smearedCharge χ 0 α :=
        norm_integral_le_of_norm_le ((hi.norm.indicator measurableSet_ball).const_mul 2)
          (Eventually.of_forall hb)
    _ = 2 * ∫ y in ball x ε, ‖pointField (x - y)‖ ∂smearedCharge χ 0 α := by
      rw [integral_const_mul, integral_indicator measurableSet_ball]
    _ ≤ 2 * ((M / α ^ 2) * (2 * Real.pi * ε)) := by
      gcongr
      exact integral_local_pointField_le hχ hM hα hε x
    _ = 4 * Real.pi * (M / α ^ 2) * ε := by ring

/-- Continuity of the convolved point field from its local integrability and the
bounded density. The argument precedes the radial flux calculation. -/
theorem continuous_convolvedField (hχ : IsMollifier χ) (hα : 0 < α) :
    Continuous (convolvedField χ 0 α) := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  have hU : TendstoUniformly (cutoffConvolution χ α) (convolvedField χ 0 α) (𝓝[>] (0 : ℝ)) := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    have ht : Tendsto (fun δ : ℝ => 4 * Real.pi * (M / α ^ 2) * δ) (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto (0 : ℝ))).const_mul
        (4 * Real.pi * (M / α ^ 2))
    filter_upwards [self_mem_nhdsWithin, ht.eventually (gt_mem_nhds hε)] with δ hδ hd
    intro x
    rw [dist_eq_norm, norm_sub_rev]
    exact (norm_cutoffConvolution_sub_le hχ hM hα hδ x).trans_lt hd
  have hc : ∀ᶠ δ in 𝓝[>] (0 : ℝ), Continuous (cutoffConvolution χ α δ) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact continuous_cutoffConvolution hχ α hδ
  exact hU.continuous hc.frequently

/-- Continuity for an arbitrary source centre, by translation. -/
theorem continuous_convolvedField_center (hχ : IsMollifier χ) (z : ℂ) (hα : 0 < α) :
    Continuous (convolvedField χ z α) := by
  have he : convolvedField χ z α = fun x => convolvedField χ 0 α (x - z) :=
    funext (convolvedField_translate χ z α)
  rw [he]
  exact (continuous_convolvedField hχ hα).comp (continuous_sub_right z)

end MultipoleBKT.RouteFlux

end
