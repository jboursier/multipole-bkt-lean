/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.Newton

/-!
# The smeared kernel `g_λ`

Properties of `g_λ(w) = ∬ g(x - y) dδ_0^{(λ)}(x) dδ_w^{(λ)}(y)` (`smearedKernel χ lam w`, equation (2.6)) for an admissible mollifier `χ`
and `λ > 0`, with `g = logKernel`. The proofs combine Fubini
(`smearedKernel_eq_integral_potential`: `g_λ(w) = ∫ U_{w,λ} dδ_0^{(λ)}`) with Newton's theorem for
one smeared charge (`MultipoleBKT.Potential.Newton`).

* `integral_logKernel_prod_smearedCharge` : the pair interaction of `δ_z^{(λ)}` and `δ_w^{(λ)}` is
  `g_λ(w - z)`.
* `smearedKernel_eq_logKernel`: `g_λ(w) = g(w)` for `|w| ≥ 2λ`.
* `smearedKernel_le_logKernel` : `g_λ(w) ≤ g(w)` for `w ≠ 0`; `smearedKernel_le` :
  `g_λ(w) ≤ g(λ) + c_χ` for all `w`, with `c_χ = ∫ g dδ_0^{(1)}`.
* `smearedKernel_ofReal_mul` : scaling `g_λ(λ w) = g(λ) + g_1(w)`, and
  `smearedKernel_eq_logKernel_add`, `smearedKernel_zero` (equation (2.4): `g_λ(0) = g(λ) + κ`).
* `smearedKernel_eq_of_norm_eq`, `smearedKernel_ofReal_norm`, `smearedKernel_neg` : `g_λ` is radial
  and even (`map_mul_smearedCharge`: rotations about `0` move the centres).
* `continuous_smearedKernel` : `g_λ` is continuous.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT

variable {χ : ℂ → ℝ} {lam : ℝ}

/-! ### Change of variables on products -/

/-- Change of variables on a product of two pushforwards by the same measurable embedding. -/
theorem integral_prod_map_measurableEmbedding {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℂ → ℂ} (hf : MeasurableEmbedding f) (μ ν : Measure ℂ) [SFinite μ]
    [SFinite ν] (g : ℂ × ℂ → E) :
    ∫ p, g p ∂(μ.map f).prod (ν.map f) = ∫ p, g (f p.1, f p.2) ∂μ.prod ν := by
  rw [Measure.map_prod_map μ ν hf.measurable hf.measurable]
  exact (hf.prodMap hf).integral_map g

/-- Translation invariance: the pair interaction of `δ_z^{(λ)}` and `δ_w^{(λ)}` is `g_λ(w - z)`. -/
theorem integral_logKernel_prod_smearedCharge (χ : ℂ → ℝ) (z w : ℂ) (lam : ℝ) :
    ∫ p : ℂ × ℂ, logKernel (p.1 - p.2) ∂(smearedCharge χ z lam).prod (smearedCharge χ w lam) =
      smearedKernel χ lam (w - z) := by
  have h1 : smearedCharge χ z lam = (smearedCharge χ 0 lam).map (· + z) := by
    rw [map_add_right_smearedCharge, zero_add]
  have h2 : smearedCharge χ w lam = (smearedCharge χ (w - z) lam).map (· + z) := by
    rw [map_add_right_smearedCharge, sub_add_cancel]
  rw [h1, h2, integral_prod_map_measurableEmbedding (measurableEmbedding_addRight z)]
  simp [smearedKernel]

/-! ### `g_λ` as an integral of the potential -/

/-- Fubini: `g_λ(w) = ∫ U_{w,λ}(x) dδ_0^{(λ)}(x)` with `U_{w,λ}(x) = ∫ g(x - y) dδ_w^{(λ)}(y)`. -/
theorem smearedKernel_eq_integral_potential (hχ : IsMollifier χ) (lam : ℝ) (w : ℂ) :
    smearedKernel χ lam w =
      ∫ x, (∫ y, logKernel (x - y) ∂smearedCharge χ w lam) ∂smearedCharge χ 0 lam := by
  have := isFiniteMeasure_smearedCharge hχ w lam
  exact integral_prod _ (integrable_logKernel_prod_smearedCharge hχ 0 w lam lam)

/-- The potential `x ↦ U_{w,λ}(x)` is integrable for `δ_0^{(λ)}`. -/
theorem integrable_potential_smearedCharge (hχ : IsMollifier χ) (lam : ℝ) (w : ℂ) :
    Integrable (fun x => ∫ y, logKernel (x - y) ∂smearedCharge χ w lam)
      (smearedCharge χ 0 lam) := by
  have := isFiniteMeasure_smearedCharge hχ w lam
  exact (integrable_logKernel_prod_smearedCharge hχ 0 w lam lam).integral_prod_left

/-! ### `g_λ(w) = g(w)` for `|w| ≥ 2λ` -/

/-- The display after (2.6): `g_λ(w) = g(w)` for `|w| ≥ 2λ` (Newton's theorem applied twice). -/
theorem smearedKernel_eq_logKernel (hχ : IsMollifier χ) (hlam : 0 < lam) {w : ℂ}
    (hw : 2 * lam ≤ ‖w‖) : smearedKernel χ lam w = logKernel w := by
  rw [smearedKernel_eq_integral_potential hχ lam w]
  have h1 : ∀ᵐ x ∂smearedCharge χ 0 lam,
      ∫ y, logKernel (x - y) ∂smearedCharge χ w lam = logKernel (w - x) := by
    filter_upwards [ae_mem_closedBall_smearedCharge hχ hlam] with x hx
    have hx' : ‖x‖ ≤ lam := by simpa using hx
    rw [integral_logKernel_sub_smearedCharge_of_le hχ hlam, TwoComponentCoulomb.logKernel,
      TwoComponentCoulomb.logKernel, norm_sub_rev]
    have h3 := norm_sub_norm_le w x
    rw [norm_sub_rev x w]
    linarith
  rw [integral_congr_ae h1]
  have h2 := integral_logKernel_sub_smearedCharge_of_le hχ (x := w) (z := 0) hlam
    (by rw [sub_zero]; linarith)
  rw [sub_zero] at h2
  exact h2

/-! ### Upper bounds -/

/-- `g_λ(w) ≤ g(w)` for `w ≠ 0`. -/
theorem smearedKernel_le_logKernel (hχ : IsMollifier χ) (hlam : 0 < lam) {w : ℂ} (hw : w ≠ 0) :
    smearedKernel χ lam w ≤ logKernel w := by
  rw [smearedKernel_eq_integral_potential hχ lam w]
  calc ∫ x, (∫ y, logKernel (x - y) ∂smearedCharge χ w lam) ∂smearedCharge χ 0 lam
      ≤ ∫ x, logKernel (w - x) ∂smearedCharge χ 0 lam := by
        refine integral_mono_ae (integrable_potential_smearedCharge hχ lam w) ?_ ?_
        · refine (integrable_logKernel_sub_smearedCharge hχ w 0 lam).congr
            (Filter.Eventually.of_forall fun x => ?_)
          simp [TwoComponentCoulomb.logKernel, norm_sub_rev]
        · filter_upwards [ae_ne_smearedCharge χ 0 w lam] with x hx
          have h := integral_logKernel_sub_smearedCharge_le hχ hx hlam
          simpa [TwoComponentCoulomb.logKernel, norm_sub_rev] using h
    _ ≤ logKernel w := by
        simpa using integral_logKernel_sub_smearedCharge_le hχ (x := w) (z := 0) hw hlam

/-- Uniform upper bound: `g_λ(w) ≤ g(λ) + c_χ` for every `w`, with the explicit constant
`c_χ = ∫ g dδ_0^{(1)} = ∫ g χ`. -/
theorem smearedKernel_le (hχ : IsMollifier χ) (hlam : 0 < lam) (w : ℂ) :
    smearedKernel χ lam w ≤ logKernel (lam : ℂ) + ∫ y, logKernel y ∂smearedCharge χ 0 1 := by
  have hprob : IsProbabilityMeasure (smearedCharge χ 0 lam) :=
    isProbabilityMeasure_smearedCharge hχ 0 hlam
  rw [smearedKernel_eq_integral_potential hχ lam w,
    ← integral_logKernel_sub_center_smearedCharge hχ w hlam]
  calc ∫ x, (∫ y, logKernel (x - y) ∂smearedCharge χ w lam) ∂smearedCharge χ 0 lam
      ≤ ∫ _, (∫ y, logKernel (y - w) ∂smearedCharge χ w lam) ∂smearedCharge χ 0 lam :=
        integral_mono (integrable_potential_smearedCharge hχ lam w) (integrable_const _)
          fun x => integral_logKernel_sub_smearedCharge_le_center hχ x w hlam
    _ = ∫ y, logKernel (y - w) ∂smearedCharge χ w lam := by
        rw [integral_const, probReal_univ, one_smul]

/-! ### Scaling -/

/-- Scaling (as in (3.35)): `g_λ(λ w) = g(λ) + g_1(w)` for `λ > 0`. -/
theorem smearedKernel_ofReal_mul (hχ : IsMollifier χ) (hlam : 0 < lam) (w : ℂ) :
    smearedKernel χ lam ((lam : ℂ) * w) = logKernel (lam : ℂ) + smearedKernel χ 1 w := by
  have hc : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hlam.ne'
  have e0 : smearedCharge χ 0 lam = (smearedCharge χ 0 1).map (fun x => (lam : ℂ) * x) := by
    rw [smearedCharge_eq_map hχ 0 hlam]
    simp
  have e1 : smearedCharge χ ((lam : ℂ) * w) lam =
      (smearedCharge χ w 1).map (fun x => (lam : ℂ) * x) := by
    rw [smearedCharge_eq_map hχ _ hlam, smearedCharge_eq_map hχ w one_pos,
      Measure.map_map (measurable_const_mul _) (by fun_prop)]
    congr 1
    funext x
    simp only [Function.comp_apply, Complex.ofReal_one, one_mul]
    ring
  have := isProbabilityMeasure_smearedCharge hχ 0 one_pos
  have := isProbabilityMeasure_smearedCharge hχ w one_pos
  unfold smearedKernel
  rw [e0, e1, integral_prod_map_measurableEmbedding (measurableEmbedding_mulLeft₀ hc)]
  have hae : ∀ᵐ p ∂(smearedCharge χ 0 1).prod (smearedCharge χ w 1),
      logKernel ((lam : ℂ) * p.1 - (lam : ℂ) * p.2) =
        logKernel (lam : ℂ) + logKernel (p.1 - p.2) := by
    filter_upwards [ae_prod_smearedCharge_ne χ 0 w 1 1] with p hp
    rw [← mul_sub, logKernel_ofReal_mul hlam (sub_ne_zero.2 hp)]
  rw [integral_congr_ae hae, integral_add (integrable_const _)
    (integrable_logKernel_prod_smearedCharge hχ 0 w 1 1), integral_const, probReal_univ,
    one_smul]

/-- Scaling: `g_λ(w) = g(λ) + g_1(w / λ)` for `λ > 0`. -/
theorem smearedKernel_eq_logKernel_add (hχ : IsMollifier χ) (hlam : 0 < lam) (w : ℂ) :
    smearedKernel χ lam w = logKernel (lam : ℂ) + smearedKernel χ 1 (w / lam) := by
  have hc : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hlam.ne'
  rw [← smearedKernel_ofReal_mul hχ hlam, mul_div_cancel₀ _ hc]

/-- Equation (2.4): `g_λ(0) = g(λ) + κ` for `λ > 0`. -/
theorem smearedKernel_zero (hχ : IsMollifier χ) (hlam : 0 < lam) :
    smearedKernel χ lam 0 = logKernel (lam : ℂ) + kappa χ := by
  rw [smearedKernel_eq_logKernel_add hχ hlam, zero_div, kappa_eq_smearedKernel]

/-! ### Radial symmetry -/

/-- Multiplication by a unit complex number `u` maps `δ_z^{(λ)}` to `δ_{u z}^{(λ)}`. -/
theorem map_mul_smearedCharge (hχ : IsMollifier χ) (z : ℂ) (lam : ℝ) {u : ℂ} (hu : ‖u‖ = 1) :
    (smearedCharge χ z lam).map (fun x => u * x) = smearedCharge χ (u * z) lam := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hvol : (volume : Measure ℂ).map (fun x => u * x) = volume := by
    have h := (measurePreserving_rotate 0 hu).map_eq
    simpa using h
  rw [smearedCharge_eq_withDensity, smearedCharge_eq_withDensity]
  refine map_withDensity_of_measurableEmbedding (measurableEmbedding_mulLeft₀ hu0) hvol fun x => ?_
  have h : χ ((u * x - u * z) / (lam : ℂ)) = χ ((x - z) / (lam : ℂ)) :=
    hχ.radial (by rw [← mul_sub, mul_div_assoc, norm_mul, hu, one_mul])
  show _ = ENNReal.ofReal ((lam ^ 2)⁻¹ * χ ((u * x - u * z) / (lam : ℂ)))
  rw [h]
  rfl

/-- `g_λ(u w) = g_λ(w)` for `‖u‖ = 1`. -/
theorem smearedKernel_mul_of_norm_eq_one (hχ : IsMollifier χ) (lam : ℝ) (w : ℂ) {u : ℂ}
    (hu : ‖u‖ = 1) : smearedKernel χ lam (u * w) = smearedKernel χ lam w := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have := isFiniteMeasure_smearedCharge hχ 0 lam
  have := isFiniteMeasure_smearedCharge hχ w lam
  have e0 : smearedCharge χ 0 lam = (smearedCharge χ 0 lam).map (fun x => u * x) := by
    rw [map_mul_smearedCharge hχ 0 lam hu, mul_zero]
  unfold smearedKernel
  conv_lhs => rw [← map_mul_smearedCharge hχ w lam hu, e0,
    integral_prod_map_measurableEmbedding (measurableEmbedding_mulLeft₀ hu0)]
  congr 1
  funext p
  simp only [TwoComponentCoulomb.logKernel, ← mul_sub, norm_mul, hu, one_mul]

/-- `g_λ` is radial: `g_λ(w) = g_λ(w')` whenever `|w| = |w'|`. -/
theorem smearedKernel_eq_of_norm_eq (hχ : IsMollifier χ) (lam : ℝ) {w w' : ℂ}
    (h : ‖w‖ = ‖w'‖) : smearedKernel χ lam w = smearedKernel χ lam w' := by
  rcases eq_or_ne w 0 with rfl | hw
  · rw [norm_zero, eq_comm, norm_eq_zero] at h
    rw [h]
  have hw' : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  have hu : ‖w' / w‖ = 1 := by rw [norm_div, ← h, div_self hw']
  rw [← smearedKernel_mul_of_norm_eq_one hχ lam w hu, div_mul_cancel₀ _ hw]

/-- `g_λ(w) = g_λ(|w|)`. -/
theorem smearedKernel_ofReal_norm (hχ : IsMollifier χ) (lam : ℝ) (w : ℂ) :
    smearedKernel χ lam (‖w‖ : ℂ) = smearedKernel χ lam w :=
  smearedKernel_eq_of_norm_eq hχ lam (by simp)

/-- `g_λ` is even. -/
theorem smearedKernel_neg (hχ : IsMollifier χ) (lam : ℝ) (w : ℂ) :
    smearedKernel χ lam (-w) = smearedKernel χ lam w :=
  smearedKernel_eq_of_norm_eq hχ lam (norm_neg w)

/-! ### Continuity -/

/-- `g_λ` is continuous, for `λ > 0`. -/
theorem continuous_smearedKernel (hχ : IsMollifier χ) (hlam : 0 < lam) :
    Continuous (smearedKernel χ lam) := by
  set Φ : ℝ → ℝ := fun s => ∫ y, -Real.log (max s ‖y‖) ∂smearedCharge χ 0 lam with hΦ
  have hΦc : Continuous Φ := continuous_integral_neg_log_max_smearedCharge hχ lam
  have hprob : IsProbabilityMeasure (smearedCharge χ 0 lam) :=
    isProbabilityMeasure_smearedCharge hχ 0 hlam
  have hfun : smearedKernel χ lam = fun w => ∫ x, Φ ‖x - w‖ ∂smearedCharge χ 0 lam := by
    funext w
    rw [smearedKernel_eq_integral_potential hχ lam w]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact integral_logKernel_sub_smearedCharge_eq_profile hχ x w hlam
  rw [hfun, continuous_iff_continuousAt]
  intro w₀
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc (a := (0 : ℝ)) (b := lam + ‖w₀‖ + 1)) hΦc.continuousOn
  refine continuousAt_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const B) ?_
  · exact Filter.Eventually.of_forall fun w =>
      (hΦc.comp (by fun_prop : Continuous fun x : ℂ => ‖x - w‖)).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds w₀ one_pos] with w hw
    filter_upwards [ae_mem_closedBall_smearedCharge hχ hlam] with x hx
    refine hB _ ⟨norm_nonneg _, ?_⟩
    have h1 : ‖x‖ ≤ lam := by simpa using hx
    have h2 : ‖w - w₀‖ < 1 := by rwa [mem_ball_iff_norm] at hw
    calc ‖x - w‖ = ‖x - w₀ - (w - w₀)‖ := by congr 1; ring
      _ ≤ ‖x - w₀‖ + ‖w - w₀‖ := norm_sub_le _ _
      _ ≤ ‖x‖ + ‖w₀‖ + ‖w - w₀‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ lam + ‖w₀‖ + 1 := by linarith
  · exact Filter.Eventually.of_forall fun x =>
      (hΦc.comp (by fun_prop : Continuous fun w : ℂ => ‖x - w‖)).continuousAt

end MultipoleBKT

end
