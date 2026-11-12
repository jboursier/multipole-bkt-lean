/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Energy.RouteGreen.Scaling
public import MultipoleBKT.Energy.RouteNeumann.GreenAverage

/-!
# Green superposition for the smeared Neumann source

Integrate the Green source equation against each smeared charge, as in
the discussion after (3.19).
The compensating density cancels because both charges have mass one.
The explicit field formula only computes the resulting Green integral.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace ComplexConjugate

namespace MultipoleBKT.RouteNeumann

variable {χ : ℂ → ℝ} {lam τ : ℝ}

/-- The rescaled Green gradient decomposes into its pole, image and
compensator, (3.19). -/
theorem discField_decomposition (hτ : 0 < τ) (z w v : ℂ) :
    RouteGreen.discField z τ w v =
      -((‖w - v‖ ^ 2)⁻¹ : ℝ) • (w - v) + screenedImageField z τ v w +
        (τ⁻¹ * τ⁻¹) • (w - z) := by
  unfold RouteGreen.discField RouteGreen.field
  rw [smul_add, smul_add, ← screenedImageField_rescale hτ]
  congr 1
  · congr 1
    rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hτ), mul_pow, mul_inv_rev, inv_pow, inv_inv,
      smul_smul, smul_smul]
    congr 1
    field_simp
  · rw [smul_smul]

/-- Integrability of the Green gradient in the smeared source variable,
equation (3.19). The pole is locally integrable. -/
theorem integrable_discField_smearedCharge (hχ : IsMollifier χ) (hlam : 0 < lam)
    {z a w : ℂ} (hτ : 0 < τ) (hw : ‖w - z‖ ≤ τ)
    (ha : ‖a - z‖ + lam < τ) :
    Integrable (fun v => RouteGreen.discField z τ w v) (smearedCharge χ a lam) := by
  let := isProbabilityMeasure_smearedCharge hχ a hlam
  have hi : Integrable (fun v => screenedImageField z τ v w) (smearedCharge χ a lam) := by
    apply integrable_on_source_disc hχ hlam
    intro v hv
    apply (hasDerivAt_screenedImageField_source
      (screenedImage_denom_ne_zero ?_)).continuousAt.continuousWithinAt
    rw [mem_closedBall, dist_eq_norm] at hv
    have hvz := norm_sub_le_norm_sub_add_norm_sub v a z
    have := mul_le_mul_of_nonneg_right hw (norm_nonneg (v - z))
    nlinarith
  simp_rw [discField_decomposition hτ]
  exact ((integrable_gradLogKernel_sub_smearedCharge hχ w a hlam).add hi).add
    (integrable_const _)

/-- The gradient obtained by Green superposition, equation (3.19). -/
noncomputable def greenField (χ : ℂ → ℝ) (lam τ : ℝ) (d : ℂ × ℂ) (w : ℂ) : ℂ :=
  (∫ v, RouteGreen.discField (dipoleMidpoint d) τ w v ∂smearedCharge χ d.1 lam) -
    ∫ v, RouteGreen.discField (dipoleMidpoint d) τ w v ∂smearedCharge χ d.2 lam

/-- Computing the Green integral gives the explicit screened field. This
identity supplies regularity; the source equation is that preceding (3.19). -/
theorem greenField_eq_screenedField (hχ : IsMollifier χ) (hlam : 0 < lam)
    {d : ℂ × ℂ} (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) {w : ℂ}
    (hw : ‖w - dipoleMidpoint d‖ ≤ τ) :
    greenField χ lam τ d w = screenedField χ lam τ d w := by
  have ht := pos_of_screening hlam hτ
  have hr := norm_le_of_screening hτ
  have hl := lam_le_of_screening hτ
  have havg (a : ℂ) (ha : ‖a - dipoleMidpoint d‖ = ‖d.2 - d.1‖ / 2) :
      (∫ v, RouteGreen.discField (dipoleMidpoint d) τ w v ∂smearedCharge χ a lam) =
        smearedField χ lam (w - a) + screenedImageField (dipoleMidpoint d) τ a w +
          (τ⁻¹ * τ⁻¹) • (w - dipoleMidpoint d) := by
    let := isProbabilityMeasure_smearedCharge hχ a hlam
    have ha' : ‖a - dipoleMidpoint d‖ + lam < τ := by rw [ha]; linarith
    have hfull := integrable_discField_smearedCharge hχ hlam ht hw ha'
    have hp := integrable_gradLogKernel_sub_smearedCharge hχ w a hlam
    have hi : Integrable (fun v => screenedImageField (dipoleMidpoint d) τ v w)
        (smearedCharge χ a lam) := by
      have := (hfull.sub hp).sub (integrable_const ((τ⁻¹ * τ⁻¹) • (w - dipoleMidpoint d)))
      convert this using 1
      funext v
      dsimp only [Pi.sub_apply]
      rw [discField_decomposition ht]
      abel
    simp_rw [discField_decomposition ht]
    have hpi : Integrable (fun v => -((‖w - v‖ ^ 2)⁻¹ : ℝ) • (w - v) +
        screenedImageField (dipoleMidpoint d) τ v w) (smearedCharge χ a lam) := hp.add hi
    rw [integral_add hpi (integrable_const _), integral_add hp hi,
      integral_gradLogKernel_sub_smearedCharge hχ w a hlam,
      integral_screenedImageField_smearedCharge hχ hlam ht hw ha',
      integral_const, probReal_univ, one_smul]
  rw [greenField, havg _ (norm_fst_sub_dipoleMidpoint d),
    havg _ (norm_snd_sub_dipoleMidpoint d)]
  simp only [screenedField, dipoleField, screenedCorrectionField]
  abel

/-- Superposition preserves the zero Neumann normal data of the Green
kernel, as in the display after (3.19). -/
theorem inner_greenField_eq_zero (hχ : IsMollifier χ) (hlam : 0 < lam)
    {d : ℂ × ℂ} (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ) {w : ℂ}
    (hw : ‖w - dipoleMidpoint d‖ = τ) :
    inner ℝ (w - dipoleMidpoint d) (greenField χ lam τ d w) = 0 := by
  have ht := pos_of_screening hlam hτ
  have hr := norm_le_of_screening hτ
  have hl := lam_le_of_screening hτ
  have havg (a : ℂ) (ha : ‖a - dipoleMidpoint d‖ = ‖d.2 - d.1‖ / 2) :
      inner ℝ (w - dipoleMidpoint d)
        (∫ v, RouteGreen.discField (dipoleMidpoint d) τ w v ∂smearedCharge χ a lam) = 0 := by
    have ha' : ‖a - dipoleMidpoint d‖ + lam < τ := by rw [ha]; linarith
    have hi := integrable_discField_smearedCharge hχ hlam ht hw.le ha'
    have he := (innerSL ℝ (w - dipoleMidpoint d)).integral_comp_comm hi
    simp only [innerSL_apply_apply] at he
    rw [← he]
    have hz : (fun v => inner ℝ (w - dipoleMidpoint d)
        (RouteGreen.discField (dipoleMidpoint d) τ w v)) =ᵐ[smearedCharge χ a lam]
        fun _ => 0 := by
      filter_upwards [ae_mem_closedBall_smearedCharge hχ hlam] with v hv
      have hvz : ‖v - dipoleMidpoint d‖ < τ := by
        rw [mem_closedBall, dist_eq_norm] at hv
        have := norm_sub_le_norm_sub_add_norm_sub v a (dipoleMidpoint d)
        linarith
      have h := RouteGreen.disc_boundary ht hw hvz
      rw [real_inner_smul_left] at h
      exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero ht.ne')
    rw [integral_congr_ae hz, integral_zero]
  rw [greenField, inner_sub_right, havg _ (norm_fst_sub_dipoleMidpoint d),
    havg _ (norm_snd_sub_dipoleMidpoint d), sub_self]

/-- Fubini integrability for a tested Green gradient. The pole uses local
integrability of the logarithmic gradient. The image and compensator are
continuous on the product of the closed disc and the source support. -/
theorem integrable_discField_test_prod (hχ : IsMollifier χ) (hlam : 0 < lam)
    {z a : ℂ} (hτ : 0 < τ) (ha : ‖a - z‖ + lam < τ)
    {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ) :
    Integrable (fun p : ℂ × ℂ => fderiv ℝ ξ p.1 (RouteGreen.discField z τ p.1 p.2))
      ((volume.restrict (ball z τ)).prod (smearedCharge χ a lam)) := by
  let := isProbabilityMeasure_smearedCharge hχ a hlam
  have hp := (integrable_fderiv_apply_gradLogKernel_sub_prod_smearedCharge hχ hξ hc a hlam).mono_measure
     (Measure.prod_mono (Measure.restrict_le_self (s := ball z τ)) le_rfl)
  have hreg : ContinuousOn (fun p : ℂ × ℂ => fderiv ℝ ξ p.1
      (screenedImageField z τ p.2 p.1 + (τ⁻¹ * τ⁻¹) • (p.1 - z)))
      (closedBall z τ ×ˢ closedBall a lam) := by
    apply ((hξ.continuous_fderiv one_ne_zero).comp continuous_fst).continuousOn.clm_apply
    apply ContinuousOn.add _ (by fun_prop)
    intro p hp
    have hden : (τ : ℂ) ^ 2 - conj (p.1 - z) * (p.2 - z) ≠ 0 := by
      apply screenedImage_denom_ne_zero
      have hw := hp.1
      have hv := hp.2
      rw [mem_closedBall, dist_eq_norm] at hw hv
      have hvz := norm_sub_le_norm_sub_add_norm_sub p.2 a z
      have := mul_le_mul_of_nonneg_right hw (norm_nonneg (p.2 - z))
      nlinarith
    exact ((by fun_prop : ContinuousAt (fun p : ℂ × ℂ => p.2 - z) p).div
      (by fun_prop) hden).continuousWithinAt
  have hi := hreg.integrableOn_compact
    ((isCompact_closedBall z τ).prod (isCompact_closedBall a lam))
    (μ := volume.prod (smearedCharge χ a lam))
  rw [IntegrableOn, ← Measure.prod_restrict,
    Measure.restrict_eq_self_of_ae_mem (ae_mem_closedBall_smearedCharge hχ hlam)] at hi
  have hi' := hi.mono_measure
    (Measure.prod_mono (Measure.restrict_mono ball_subset_closedBall le_rfl) le_rfl)
  convert hp.add hi' using 1
  funext p
  dsimp only [Pi.add_apply]
  rw [discField_decomposition hτ, map_add, map_add, map_add]
  ring

/-- Superposing one Green source equation gives its smeared source and the
same compensating density, as in the Green problem preceding (3.19). -/
theorem integral_discField_smeared_source (hχ : IsMollifier χ) (hlam : 0 < lam)
    {z a : ℂ} (hτ : 0 < τ) (ha : ‖a - z‖ + lam < τ)
    {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ)
    (hs : tsupport ξ ⊆ ball z τ) :
    (∫ w in ball z τ, fderiv ℝ ξ w
      (∫ v, RouteGreen.discField z τ w v ∂smearedCharge χ a lam)) =
      2 * Real.pi * ((∫ v, ξ v ∂smearedCharge χ a lam) -
        ∫ w, RouteGreen.discDensity τ * ξ w) := by
  let := isProbabilityMeasure_smearedCharge hχ a hlam
  have hp := integrable_discField_test_prod hχ hlam hτ ha hξ hc
  have he : ∀ w ∈ ball z τ, fderiv ℝ ξ w
      (∫ v, RouteGreen.discField z τ w v ∂smearedCharge χ a lam) =
      ∫ v, fderiv ℝ ξ w (RouteGreen.discField z τ w v) ∂smearedCharge χ a lam := by
    intro w hw
    exact ((fderiv ℝ ξ w).integral_comp_comm
      (integrable_discField_smearedCharge hχ hlam hτ
        (by simpa only [dist_eq_norm] using (mem_ball.mp hw).le) ha)).symm
  rw [setIntegral_congr_fun measurableSet_ball he, integral_integral_swap hp]
  have heq : ∀ᵐ v ∂smearedCharge χ a lam,
      (∫ w in ball z τ, fderiv ℝ ξ w (RouteGreen.discField z τ w v)) =
        2 * Real.pi * (ξ v - ∫ w, RouteGreen.discDensity τ * ξ w) := by
    filter_upwards [ae_mem_closedBall_smearedCharge hχ hlam] with v hv
    have hvz : ‖v - z‖ < τ := by
      rw [mem_closedBall, dist_eq_norm] at hv
      have := norm_sub_le_norm_sub_add_norm_sub v a z
      linarith
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun w hw => ?_)]
    · exact RouteGreen.disc_source hτ hvz hξ hc hs
    · rw [fderiv_of_notMem_tsupport ℝ (fun h => hw (hs h)), zero_apply]
  rw [integral_congr_ae heq, integral_const_mul,
    integral_sub (hξ.continuous.integrable_of_hasCompactSupport hc
      (μ := smearedCharge χ a lam)) (integrable_const _),
    integral_const, probReal_univ, one_smul]

/-- Neutral Green superposition solves the smeared source equation.
The compensating densities cancel by equal unit masses, as in the discussion after (3.19). -/
theorem integral_greenField_source (hχ : IsMollifier χ) (hlam : 0 < lam)
    {d : ℂ × ℂ} (hτ : 8 * max ‖d.2 - d.1‖ lam ≤ τ)
    {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ)
    (hs : tsupport ξ ⊆ ball (dipoleMidpoint d) τ) :
    (∫ w in ball (dipoleMidpoint d) τ, fderiv ℝ ξ w (greenField χ lam τ d w)) =
      2 * Real.pi * ((∫ v, ξ v ∂smearedCharge χ d.1 lam) -
        ∫ v, ξ v ∂smearedCharge χ d.2 lam) := by
  have ht := pos_of_screening hlam hτ
  have hr := norm_le_of_screening hτ
  have hl := lam_le_of_screening hτ
  have ha : ‖d.1 - dipoleMidpoint d‖ + lam < τ := by
    rw [norm_fst_sub_dipoleMidpoint]
    linarith
  have hb : ‖d.2 - dipoleMidpoint d‖ + lam < τ := by
    rw [norm_snd_sub_dipoleMidpoint]
    linarith
  have hia := (integrable_discField_test_prod hχ hlam ht ha hξ hc).integral_prod_left
  have hib := (integrable_discField_test_prod hχ hlam ht hb hξ hc).integral_prod_left
  have he (a : ℂ) (ha : ‖a - dipoleMidpoint d‖ + lam < τ) :
      (fun w => fderiv ℝ ξ w
        (∫ v, RouteGreen.discField (dipoleMidpoint d) τ w v ∂smearedCharge χ a lam)) =ᵐ[
          volume.restrict (ball (dipoleMidpoint d) τ)]
      fun w => ∫ v, fderiv ℝ ξ w (RouteGreen.discField (dipoleMidpoint d) τ w v)
        ∂smearedCharge χ a lam := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    exact ((fderiv ℝ ξ w).integral_comp_comm
      (integrable_discField_smearedCharge hχ hlam ht
        (by simpa only [dist_eq_norm] using (mem_ball.mp hw).le) ha)).symm
  simp only [greenField, map_sub]
  rw [integral_sub (hia.congr (he d.1 ha).symm) (hib.congr (he d.2 hb).symm),
    integral_discField_smeared_source hχ hlam ht ha hξ hc hs,
    integral_discField_smeared_source hχ hlam ht hb hξ hc hs]
  ring

end MultipoleBKT.RouteNeumann
