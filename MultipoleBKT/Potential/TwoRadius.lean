/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.Kernel

/-!
# The potential `g * δ₀^{(λ)}` and the two-radius kernels `g * δ₀^{(α)} * δ₀^{(η)}`

In Section 3.1 of the paper, equation (3.2) enlarges the radii of the
smeared charges independently, so the pair interactions of Proposition 3.3
(equation (3.6)) and of Section 5 involve the kernels `g * δ₀^{(α)} * δ₀^{(η)}` with two
different radii; Lemma 3.1 concerns `g̃₁ = g * δ₀^{(1)}`. Here `g = logKernel`,
`δ_z^{(λ)} = smearedCharge χ z λ` and `χ` is an admissible mollifier (`IsMollifier χ`).

Definitions:

* `smearedPotential χ lam x = (g * δ₀^{(λ)})(x) = ∫ g(x - y) dδ₀^{(λ)}(y)`.
* `twoRadiusKernel χ α η z = ∬ g(x - y) dδ₀^{(α)}(x) dδ_z^{(η)}(y)`, which is
  `(g * δ₀^{(α)} * δ₀^{(η)})(z)` (`twoRadiusKernel_eq_integral_conv`:
  `twoRadiusKernel χ α η z = ∬ g(z - a - b) dδ₀^{(α)}(a) dδ₀^{(η)}(b)`, the literal convolution).

Main results:

* `twoRadiusKernel_self` : `twoRadiusKernel χ λ λ = smearedKernel χ λ = g_λ` (by `rfl`).
* `integral_logKernel_prod_smearedCharge_eq_twoRadiusKernel` : the pair interaction of
  `δ_z^{(α)}` and `δ_w^{(η)}` is `twoRadiusKernel χ α η (w - z)`.
* `twoRadiusKernel_eq_integral_smearedPotential` :
  `twoRadiusKernel χ α η z = ∫ (g * δ₀^{(η)})(z - a) dδ₀^{(α)}(a)`.
* `twoRadiusKernel_comm`, `twoRadiusKernel_mul_of_norm_eq_one`, `twoRadiusKernel_eq_of_norm_eq`,
  `twoRadiusKernel_neg` : symmetry in `(α, η)`; radial and even in `z`.
* `twoRadiusKernel_eq_logKernel` : **Newton's theorem**, `twoRadiusKernel χ α η z = g(z)` for
  `|z| ≥ α + η`.
* `twoRadiusKernel_le_logKernel` (`≤ g(z)` for `z ≠ 0`), `twoRadiusKernel_le_right`,
  `twoRadiusKernel_le_left` (`≤ g(η) + c_χ`, `≤ g(α) + c_χ`, with `c_χ = ∫ g dδ₀^{(1)}`).
* `continuous_twoRadiusKernel`.
* For the potential: `smearedPotential_eq_integral_max` (radial formula),
  `smearedPotential_eq_logKernel` (Newton), `smearedPotential_le_logKernel`,
  `smearedPotential_le`, `smearedPotential_zero`, `smearedPotential_eq_of_norm_eq`,
  `smearedPotential_neg`, `continuous_smearedPotential`.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT

/-- The potential `(g * δ₀^{(λ)})(x) = ∫ g(x - y) dδ₀^{(λ)}(y)` of the smeared charge of radius `λ`
centred at `0` (Section 3.1, Lemma 3.1: `g̃₁ = g * δ₀^{(1)}`). -/
noncomputable def smearedPotential (χ : ℂ → ℝ) (lam : ℝ) (x : ℂ) : ℝ :=
  ∫ y, logKernel (x - y) ∂smearedCharge χ 0 lam

/-- The two-radius kernel `(g * δ₀^{(α)} * δ₀^{(η)})(z) = ∬ g(x - y) dδ₀^{(α)}(x) dδ_z^{(η)}(y)`
(equation (3.2), Lemma 3.2, equation (3.6)). For
`α = η = λ` it is `g_λ` (`twoRadiusKernel_self`). -/
noncomputable def twoRadiusKernel (χ : ℂ → ℝ) (α η : ℝ) (z : ℂ) : ℝ :=
  ∫ p : ℂ × ℂ, logKernel (p.1 - p.2) ∂(smearedCharge χ 0 α).prod (smearedCharge χ z η)

variable {χ : ℂ → ℝ} {lam α η : ℝ}

/-! ### Elementary facts -/

/-- `g` is even. -/
theorem logKernel_neg (x : ℂ) : logKernel (-x) = logKernel x := by
  simp [TwoComponentCoulomb.logKernel]

/-- `g_λ` is the two-radius kernel with equal radii. -/
theorem twoRadiusKernel_self (χ : ℂ → ℝ) (lam : ℝ) :
    twoRadiusKernel χ lam lam = smearedKernel χ lam := rfl

/-- `y ↦ z - y` pushes `δ₀^{(λ)}` forward to `δ_z^{(λ)}` (`χ` is even). -/
theorem map_sub_left_smearedCharge (hχ : IsMollifier χ) (z : ℂ) (lam : ℝ) :
    (smearedCharge χ 0 lam).map (fun y => z - y) = smearedCharge χ z lam := by
  have h : (fun y : ℂ => z - y) = (· + z) ∘ Neg.neg := by
    funext y
    simp only [Function.comp_apply]
    ring
  rw [h, ← Measure.map_map (measurable_add_const z) measurable_neg, map_neg_smearedCharge hχ,
    neg_zero, map_add_right_smearedCharge, zero_add]

theorem measurableEmbedding_sub_left (z : ℂ) : MeasurableEmbedding fun y : ℂ => z - y :=
  (Homeomorph.subLeft z).measurableEmbedding

/-- Changing variables in the second factor of a product measure. -/
theorem integral_prod_map_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → ℂ} (hf : MeasurableEmbedding f) (μ ν : Measure ℂ) [SFinite μ] [SFinite ν]
    (g : ℂ × ℂ → E) :
    ∫ p, g p ∂μ.prod (ν.map f) = ∫ p, g (p.1, f p.2) ∂μ.prod ν := by
  have h : μ.prod (ν.map f) = (μ.prod ν).map (Prod.map id f) := by
    rw [← Measure.map_prod_map μ ν measurable_id hf.measurable, Measure.map_id]
  rw [h, (MeasurableEmbedding.id.prodMap hf).integral_map]
  rfl

theorem integrable_prod_map_right_iff {E : Type*} [NormedAddCommGroup E] {f : ℂ → ℂ}
    (hf : MeasurableEmbedding f) (μ ν : Measure ℂ) [SFinite μ] [SFinite ν] (g : ℂ × ℂ → E) :
    Integrable g (μ.prod (ν.map f)) ↔ Integrable (fun p => g (p.1, f p.2)) (μ.prod ν) := by
  have h : μ.prod (ν.map f) = (μ.prod ν).map (Prod.map id f) := by
    rw [← Measure.map_prod_map μ ν measurable_id hf.measurable, Measure.map_id]
  rw [h, (MeasurableEmbedding.id.prodMap hf).integrable_map_iff]
  rfl

/-! ### The potential `g * δ₀^{(λ)}` -/

/-- Translation: `∫ g(x - y) dδ_z^{(λ)}(y) = (g * δ₀^{(λ)})(x - z)`. -/
theorem integral_logKernel_sub_smearedCharge_eq_smearedPotential (χ : ℂ → ℝ) (x z : ℂ)
    (lam : ℝ) :
    ∫ y, logKernel (x - y) ∂smearedCharge χ z lam = smearedPotential χ lam (x - z) := by
  have h := map_add_right_smearedCharge χ 0 z lam
  rw [zero_add] at h
  rw [← h, (measurableEmbedding_addRight z).integral_map, smearedPotential]
  congr 1
  funext y
  congr 1
  ring

/-- Radial formula: `(g * δ₀^{(λ)})(x) = ∫ -log (max |x| |y|) dδ₀^{(λ)}(y)` for `λ > 0`. -/
theorem smearedPotential_eq_integral_max (hχ : IsMollifier χ) (hlam : 0 < lam) (x : ℂ) :
    smearedPotential χ lam x = ∫ y, -Real.log (max ‖x‖ ‖y‖) ∂smearedCharge χ 0 lam := by
  have h := integral_logKernel_sub_smearedCharge_eq_profile hχ x 0 hlam
  rw [sub_zero] at h
  exact h

/-- `g * δ₀^{(λ)}` is radial. -/
theorem smearedPotential_eq_of_norm_eq (hχ : IsMollifier χ) (hlam : 0 < lam) {x x' : ℂ}
    (h : ‖x‖ = ‖x'‖) : smearedPotential χ lam x = smearedPotential χ lam x' := by
  rw [smearedPotential_eq_integral_max hχ hlam, smearedPotential_eq_integral_max hχ hlam, h]

/-- `g * δ₀^{(λ)}` is even. -/
theorem smearedPotential_neg (hχ : IsMollifier χ) (lam : ℝ) (x : ℂ) :
    smearedPotential χ lam (-x) = smearedPotential χ lam x := by
  have h := map_neg_smearedCharge hχ 0 lam
  rw [neg_zero] at h
  unfold smearedPotential
  conv_lhs => rw [← h]
  rw [measurableEmbedding_neg.integral_map]
  congr 1
  funext y
  rw [← logKernel_neg (x - y)]
  congr 1
  ring

/-- **Newton's theorem**: `(g * δ₀^{(λ)})(x) = g(x)` for `|x| ≥ λ`. -/
theorem smearedPotential_eq_logKernel (hχ : IsMollifier χ) (hlam : 0 < lam) {x : ℂ}
    (hx : lam ≤ ‖x‖) : smearedPotential χ lam x = logKernel x := by
  have h := integral_logKernel_sub_smearedCharge_of_le hχ (x := x) (z := 0) hlam
    (by rwa [sub_zero])
  rw [sub_zero] at h
  exact h

/-- `(g * δ₀^{(λ)})(x) ≤ g(x)` for `x ≠ 0`. -/
theorem smearedPotential_le_logKernel (hχ : IsMollifier χ) (hlam : 0 < lam) {x : ℂ}
    (hx : x ≠ 0) : smearedPotential χ lam x ≤ logKernel x := by
  have h := integral_logKernel_sub_smearedCharge_le hχ (x := x) (z := 0) hx hlam
  rw [sub_zero] at h
  exact h

/-- The value at the centre: `(g * δ₀^{(λ)})(0) = g(λ) + c_χ`, `c_χ = ∫ g dδ₀^{(1)}`. -/
theorem smearedPotential_zero (hχ : IsMollifier χ) (hlam : 0 < lam) :
    smearedPotential χ lam 0 = logKernel (lam : ℂ) + ∫ y, logKernel y ∂smearedCharge χ 0 1 := by
  rw [← integral_logKernel_sub_center_smearedCharge hχ 0 hlam, smearedPotential]
  congr 1
  funext y
  rw [zero_sub, sub_zero, logKernel_neg]

/-- The potential is maximal at the centre: `(g * δ₀^{(λ)})(x) ≤ g(λ) + c_χ`. -/
theorem smearedPotential_le (hχ : IsMollifier χ) (hlam : 0 < lam) (x : ℂ) :
    smearedPotential χ lam x ≤ logKernel (lam : ℂ) + ∫ y, logKernel y ∂smearedCharge χ 0 1 := by
  rw [← integral_logKernel_sub_center_smearedCharge hχ 0 hlam]
  exact integral_logKernel_sub_smearedCharge_le_center hχ x 0 hlam

/-- `g * δ₀^{(λ)}` is continuous, for `λ > 0`. -/
theorem continuous_smearedPotential (hχ : IsMollifier χ) (hlam : 0 < lam) :
    Continuous (smearedPotential χ lam) :=
  continuous_integral_logKernel_sub_smearedCharge hχ 0 hlam

/-- `g * δ₀^{(λ)}` is integrable against a smeared charge, for `λ > 0`. -/
theorem integrable_smearedPotential_comp (hχ : IsMollifier χ) (hlam : 0 < lam) {f : ℂ → ℂ}
    (hf : Continuous f) (z : ℂ) (mu : ℝ) :
    Integrable (fun a => smearedPotential χ lam (f a)) (smearedCharge χ z mu) :=
  integrable_smearedCharge_of_continuous hχ ((continuous_smearedPotential hχ hlam).comp hf) z mu

/-! ### The two-radius kernel as a convolution and as an integral of the potential -/

/-- The integrand of the convolution form is integrable. -/
theorem integrable_logKernel_conv (hχ : IsMollifier χ) (α η : ℝ) (z : ℂ) :
    Integrable (fun p : ℂ × ℂ => logKernel (z - p.1 - p.2))
      ((smearedCharge χ 0 α).prod (smearedCharge χ 0 η)) := by
  have h := integrable_logKernel_prod_smearedCharge hχ 0 z α η
  rw [← map_sub_left_smearedCharge hχ z η,
    integrable_prod_map_right_iff (measurableEmbedding_sub_left z)] at h
  refine h.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only
  rw [← logKernel_neg]
  congr 1
  ring

/-- The two-radius kernel is the convolution `(g * δ₀^{(α)} * δ₀^{(η)})(z) =
∬ g(z - a - b) dδ₀^{(α)}(a) dδ₀^{(η)}(b)`. -/
theorem twoRadiusKernel_eq_integral_conv (hχ : IsMollifier χ) (α η : ℝ) (z : ℂ) :
    twoRadiusKernel χ α η z =
      ∫ p : ℂ × ℂ, logKernel (z - p.1 - p.2)
        ∂(smearedCharge χ 0 α).prod (smearedCharge χ 0 η) := by
  unfold twoRadiusKernel
  rw [← map_sub_left_smearedCharge hχ z η,
    integral_prod_map_right (measurableEmbedding_sub_left z)]
  congr 1
  funext p
  rw [← logKernel_neg]
  congr 1
  ring

/-- `twoRadiusKernel χ α η z = ∫ (g * δ₀^{(η)})(z - a) dδ₀^{(α)}(a)`. -/
theorem twoRadiusKernel_eq_integral_smearedPotential (hχ : IsMollifier χ) (α η : ℝ) (z : ℂ) :
    twoRadiusKernel χ α η z =
      ∫ a, smearedPotential χ η (z - a) ∂smearedCharge χ 0 α := by
  have := isFiniteMeasure_smearedCharge hχ 0 η
  rw [twoRadiusKernel_eq_integral_conv hχ, integral_prod _ (integrable_logKernel_conv hχ α η z)]
  rfl

/-- Translation invariance: the pair interaction of `δ_z^{(α)}` and `δ_w^{(η)}` is
`twoRadiusKernel χ α η (w - z)`. -/
theorem integral_logKernel_prod_smearedCharge_eq_twoRadiusKernel (χ : ℂ → ℝ) (z w : ℂ)
    (α η : ℝ) :
    ∫ p : ℂ × ℂ, logKernel (p.1 - p.2) ∂(smearedCharge χ z α).prod (smearedCharge χ w η) =
      twoRadiusKernel χ α η (w - z) := by
  have h1 : smearedCharge χ z α = (smearedCharge χ 0 α).map (· + z) := by
    rw [map_add_right_smearedCharge, zero_add]
  have h2 : smearedCharge χ w η = (smearedCharge χ (w - z) η).map (· + z) := by
    rw [map_add_right_smearedCharge, sub_add_cancel]
  rw [h1, h2, integral_prod_map_measurableEmbedding (measurableEmbedding_addRight z)]
  simp [twoRadiusKernel]

/-! ### Symmetries -/

/-- Symmetry in the two radii: `g * δ₀^{(α)} * δ₀^{(η)} = g * δ₀^{(η)} * δ₀^{(α)}`. -/
theorem twoRadiusKernel_comm (hχ : IsMollifier χ) (α η : ℝ) (z : ℂ) :
    twoRadiusKernel χ α η z = twoRadiusKernel χ η α z := by
  have := isFiniteMeasure_smearedCharge hχ 0 α
  have := isFiniteMeasure_smearedCharge hχ 0 η
  rw [twoRadiusKernel_eq_integral_conv hχ, twoRadiusKernel_eq_integral_conv hχ,
    ← integral_prod_swap]
  congr 1
  funext p
  simp only [Prod.fst_swap, Prod.snd_swap]
  congr 1
  ring

/-- Rotation invariance: `twoRadiusKernel χ α η (u z) = twoRadiusKernel χ α η z` for `|u| = 1`. -/
theorem twoRadiusKernel_mul_of_norm_eq_one (hχ : IsMollifier χ) (α η : ℝ) (z : ℂ) {u : ℂ}
    (hu : ‖u‖ = 1) : twoRadiusKernel χ α η (u * z) = twoRadiusKernel χ α η z := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have := isFiniteMeasure_smearedCharge hχ 0 α
  have := isFiniteMeasure_smearedCharge hχ 0 η
  have e : ∀ mu : ℝ, smearedCharge χ 0 mu = (smearedCharge χ 0 mu).map (fun x => u * x) :=
    fun mu => by rw [map_mul_smearedCharge hχ 0 mu hu, mul_zero]
  rw [twoRadiusKernel_eq_integral_conv hχ, twoRadiusKernel_eq_integral_conv hχ, e α, e η,
    integral_prod_map_measurableEmbedding (measurableEmbedding_mulLeft₀ hu0), ← e α, ← e η]
  congr 1
  funext p
  simp only [TwoComponentCoulomb.logKernel]
  rw [show u * z - u * p.1 - u * p.2 = u * (z - p.1 - p.2) by ring, norm_mul, hu, one_mul]

/-- The two-radius kernel is radial. -/
theorem twoRadiusKernel_eq_of_norm_eq (hχ : IsMollifier χ) (α η : ℝ) {z z' : ℂ}
    (h : ‖z‖ = ‖z'‖) : twoRadiusKernel χ α η z = twoRadiusKernel χ α η z' := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [norm_zero, eq_comm, norm_eq_zero] at h
    rw [h]
  have hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
  have hu : ‖z' / z‖ = 1 := by rw [norm_div, ← h, div_self hz']
  rw [← twoRadiusKernel_mul_of_norm_eq_one hχ α η z hu, div_mul_cancel₀ _ hz]

/-- The two-radius kernel is even. -/
theorem twoRadiusKernel_neg (hχ : IsMollifier χ) (α η : ℝ) (z : ℂ) :
    twoRadiusKernel χ α η (-z) = twoRadiusKernel χ α η z :=
  twoRadiusKernel_eq_of_norm_eq hχ α η (norm_neg z)

/-! ### Newton's theorem and upper bounds -/

/-- **Newton's theorem** for two radii: `(g * δ₀^{(α)} * δ₀^{(η)})(z) = g(z)` for
`|z| ≥ α + η` (Section 3.2, the proof of Lemma 5.12). -/
theorem twoRadiusKernel_eq_logKernel (hχ : IsMollifier χ) (hα : 0 < α) (hη : 0 < η) {z : ℂ}
    (hz : α + η ≤ ‖z‖) : twoRadiusKernel χ α η z = logKernel z := by
  rw [twoRadiusKernel_eq_integral_smearedPotential hχ]
  have h1 : ∀ᵐ a ∂smearedCharge χ 0 α, smearedPotential χ η (z - a) = logKernel (z - a) := by
    filter_upwards [ae_mem_closedBall_smearedCharge hχ hα] with a ha
    have ha' : ‖a‖ ≤ α := by simpa using ha
    refine smearedPotential_eq_logKernel hχ hη ?_
    have := norm_sub_norm_le z a
    linarith
  rw [integral_congr_ae h1]
  have h2 : ∫ a, logKernel (z - a) ∂smearedCharge χ 0 α = smearedPotential χ α z := rfl
  rw [h2, smearedPotential_eq_logKernel hχ hα (by linarith)]

/-- `(g * δ₀^{(α)} * δ₀^{(η)})(z) ≤ g(z)` for `z ≠ 0`. -/
theorem twoRadiusKernel_le_logKernel (hχ : IsMollifier χ) (hα : 0 < α) (hη : 0 < η) {z : ℂ}
    (hz : z ≠ 0) : twoRadiusKernel χ α η z ≤ logKernel z := by
  rw [twoRadiusKernel_eq_integral_smearedPotential hχ]
  calc ∫ a, smearedPotential χ η (z - a) ∂smearedCharge χ 0 α
      ≤ ∫ a, logKernel (z - a) ∂smearedCharge χ 0 α := by
        refine integral_mono_ae
          (integrable_smearedPotential_comp hχ hη (continuous_const.sub continuous_id) 0 α)
          ?_ ?_
        · refine (integrable_logKernel_sub_smearedCharge hχ z 0 α).congr
            (Filter.Eventually.of_forall fun a => ?_)
          show logKernel (a - z) = logKernel (z - a)
          rw [← logKernel_neg]
          congr 1
          ring
        · filter_upwards [ae_ne_smearedCharge χ 0 z α] with a ha
          exact smearedPotential_le_logKernel hχ hη (sub_ne_zero.2 (Ne.symm ha))
    _ = smearedPotential χ α z := rfl
    _ ≤ logKernel z := smearedPotential_le_logKernel hχ hα hz

/-- Uniform upper bound: `(g * δ₀^{(α)} * δ₀^{(η)})(z) ≤ g(η) + c_χ`. -/
theorem twoRadiusKernel_le_right (hχ : IsMollifier χ) (hα : 0 < α) (hη : 0 < η) (z : ℂ) :
    twoRadiusKernel χ α η z ≤ logKernel (η : ℂ) + ∫ y, logKernel y ∂smearedCharge χ 0 1 := by
  have := isProbabilityMeasure_smearedCharge hχ 0 hα
  rw [twoRadiusKernel_eq_integral_smearedPotential hχ]
  calc ∫ a, smearedPotential χ η (z - a) ∂smearedCharge χ 0 α
      ≤ ∫ _, (logKernel (η : ℂ) + ∫ y, logKernel y ∂smearedCharge χ 0 1)
          ∂smearedCharge χ 0 α :=
        integral_mono
          (integrable_smearedPotential_comp hχ hη (continuous_const.sub continuous_id) 0 α)
          (integrable_const _) fun a => smearedPotential_le hχ hη (z - a)
    _ = logKernel (η : ℂ) + ∫ y, logKernel y ∂smearedCharge χ 0 1 := by
        rw [integral_const, probReal_univ, one_smul]

/-- Uniform upper bound: `(g * δ₀^{(α)} * δ₀^{(η)})(z) ≤ g(α) + c_χ`. -/
theorem twoRadiusKernel_le_left (hχ : IsMollifier χ) (hα : 0 < α) (hη : 0 < η) (z : ℂ) :
    twoRadiusKernel χ α η z ≤ logKernel (α : ℂ) + ∫ y, logKernel y ∂smearedCharge χ 0 1 := by
  rw [twoRadiusKernel_comm hχ]
  exact twoRadiusKernel_le_right hχ hη hα z

/-! ### Continuity -/

/-- The two-radius kernel is continuous, for `α, η > 0`. -/
theorem continuous_twoRadiusKernel (hχ : IsMollifier χ) (hα : 0 < α) (hη : 0 < η) :
    Continuous (twoRadiusKernel χ α η) := by
  have hU := continuous_smearedPotential hχ hη
  have hfun : twoRadiusKernel χ α η =
      fun z => ∫ a, smearedPotential χ η (z - a) ∂smearedCharge χ 0 α :=
    funext fun z => twoRadiusKernel_eq_integral_smearedPotential hχ α η z
  have := isProbabilityMeasure_smearedCharge hχ 0 hα
  rw [hfun, continuous_iff_continuousAt]
  intro z₀
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_closedBall (0 : ℂ) (α + ‖z₀‖ + 1)) hU.continuousOn
  refine continuousAt_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const B) ?_
  · exact Filter.Eventually.of_forall fun z =>
      (hU.comp (by fun_prop : Continuous fun a : ℂ => z - a)).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds z₀ one_pos] with z hz
    filter_upwards [ae_mem_closedBall_smearedCharge hχ hα] with a ha
    refine hB _ ?_
    have h1 : ‖a‖ ≤ α := by simpa using ha
    have h2 : ‖z - z₀‖ < 1 := by rwa [mem_ball_iff_norm] at hz
    rw [mem_closedBall_zero_iff]
    calc ‖z - a‖ = ‖(z - z₀) + z₀ - a‖ := by congr 1; ring
      _ ≤ ‖z - z₀‖ + ‖z₀‖ + ‖a‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
      _ ≤ α + ‖z₀‖ + 1 := by linarith
  · exact Filter.Eventually.of_forall fun a =>
      (hU.comp (by fun_prop : Continuous fun z : ℂ => z - a)).continuousAt

end MultipoleBKT

end
