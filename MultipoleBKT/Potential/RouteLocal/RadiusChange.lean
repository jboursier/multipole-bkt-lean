/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPoints.Decay

/-!
# Translation and radius change after insertion of a common charge

See Lemma 3.9,
(3.47). Insert the charge at the second centre with
radius equal to that at the first centre. Estimate translation with the
bounded gradient of the singly smoothed potential. Estimate radius change
by Taylor expansion at the common centre and evenness of each charge.
-/

@[expose] public section

open MeasureTheory Metric

namespace MultipoleBKT

variable {χ : ℂ → ℝ}

/-- **Second-order comparison** (Lemma 3.9):
`|K_{α,η}(z) - (g * δ₀^{(η)})(z)| ≤ 3 π M α² / η²`. The charge `δ₀^{(α)}` is even, so
`K_{α,η}(z) - (g * δ₀^{(η)})(z) = ½ ∫ (f(z + a) + f(z - a) - 2 f(z)) dδ₀^{(α)}(a)` with
`f = g * δ₀^{(η)}`, whose gradient is `3 π M / η²`-Lipschitz. -/
theorem abs_twoRadiusKernel_sub_smearedPotential_le_sq (hχ : IsMollifier χ) {M : ℝ}
    (hM : ∀ x, χ x ≤ M) {α η : ℝ} (hα : 0 < α) (hη : 0 < η) (z : ℂ) :
    |twoRadiusKernel χ α η z - smearedPotential χ η z| ≤ 3 * (Real.pi * M / η ^ 2) * α ^ 2 := by
  have := isProbabilityMeasure_smearedCharge hχ 0 hα
  have hM0 : 0 ≤ M := hχ.nonneg_of_le hM
  set μ := smearedCharge χ 0 α with hμ
  set f := smearedPotential χ η with hf
  set L := 3 * (Real.pi * M / η ^ 2) with hL
  have hL0 : 0 ≤ L := by positivity
  have hint₁ : Integrable (fun a => f (z - a)) μ :=
    integrable_smearedPotential_comp hχ hη (continuous_const.sub continuous_id) 0 α
  have hint₂ : Integrable (fun a => f (z + a)) μ :=
    integrable_smearedPotential_comp hχ hη (continuous_const.add continuous_id) 0 α
  have hneg : μ.map Neg.neg = μ := by
    have h := map_neg_smearedCharge hχ 0 α
    rwa [neg_zero] at h
  have hsym : ∫ a, f (z - a) ∂μ = ∫ a, f (z + a) ∂μ := by
    conv_lhs => rw [← hneg]
    rw [measurableEmbedding_neg.integral_map]
    simp only [sub_neg_eq_add]
  have hK : twoRadiusKernel χ α η z - f z =
      (1 / 2) * ∫ a, (f (z + a) + f (z - a) - 2 * f z) ∂μ := by
    have h1 : ∫ a, (f (z + a) + f (z - a) - 2 * f z) ∂μ =
        ∫ a, f (z + a) ∂μ + ∫ a, f (z - a) ∂μ - 2 * f z := by
      have hint₃ : Integrable (fun a => f (z + a) + f (z - a)) μ := hint₂.add hint₁
      rw [integral_sub hint₃ (integrable_const _), integral_add hint₂ hint₁,
        integral_const, probReal_univ, one_smul]
    rw [twoRadiusKernel_eq_integral_smearedPotential hχ]
    change ∫ a, f (z - a) ∂μ - f z = _
    rw [h1, ← hsym]
    ring
  have hb : ∀ᵐ a ∂μ, ‖f (z + a) + f (z - a) - 2 * f z‖ ≤ 2 * L * α ^ 2 := by
    filter_upwards [ae_mem_closedBall_smearedCharge hχ (z := 0) hα] with a ha
    rw [mem_closedBall, dist_zero_right] at ha
    have h1 := abs_sub_sub_fderiv_le_of_differentiable (differentiable_smearedPotential hχ hη)
      (norm_fderiv_smearedPotential_sub_le hχ hM hη) z a
    have h2 := abs_sub_sub_fderiv_le_of_differentiable (differentiable_smearedPotential hχ hη)
      (norm_fderiv_smearedPotential_sub_le hχ hM hη) z (-a)
    rw [norm_neg, ← sub_eq_add_neg, map_neg] at h2
    have ha2 : ‖a‖ ^ 2 ≤ α ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
    have e : f (z + a) + f (z - a) - 2 * f z =
        (f (z + a) - f z - fderiv ℝ f z a) + (f (z - a) - f z - -fderiv ℝ f z a) := by ring
    rw [Real.norm_eq_abs, e]
    calc _ ≤ |f (z + a) - f z - fderiv ℝ f z a| + |f (z - a) - f z - -fderiv ℝ f z a| :=
          abs_add_le _ _
      _ ≤ L * ‖a‖ ^ 2 + L * ‖a‖ ^ 2 := add_le_add h1 h2
      _ ≤ L * α ^ 2 + L * α ^ 2 := by gcongr
      _ = 2 * L * α ^ 2 := by ring
  have hI := norm_integral_le_of_norm_le_const hb
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at hI
  rw [hK, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  linarith

namespace RouteLocal

/-- Translation of the averaging charge identifies the kernel with the
integral of `f(x) = (g * δ₀^(η))(x - w)` against `δ_a^(α)` (the proof of Lemma 3.9). -/
theorem integral_shiftedPotential_eq_kernel (hχ : IsMollifier χ) (α η : ℝ) (a w : ℂ) :
    ∫ x, smearedPotential χ η (x - w) ∂smearedCharge χ a α =
      twoRadiusKernel χ α η (a - w) := by
  have ht := map_add_right_smearedCharge χ 0 a α
  rw [zero_add] at ht
  rw [← ht, (measurableEmbedding_addRight a).integral_map]
  have hn := map_neg_smearedCharge hχ 0 α
  rw [neg_zero] at hn
  rw [twoRadiusKernel_eq_integral_smearedPotential hχ]
  conv_rhs => rw [← hn]
  rw [measurableEmbedding_neg.integral_map]
  congr 1
  funext x
  congr 1
  ring

/-- Insert `δ_b^(α)` between `δ_a^(α)` and `δ_b^(α')`, exactly as
in the displayed decomposition before the two estimates (the proof of Lemma 3.9). -/
theorem common_radius_insertion (hχ : IsMollifier χ) (α α' η : ℝ) (a b w : ℂ) :
    twoRadiusKernel χ α η (a - w) - twoRadiusKernel χ α' η (b - w) =
      ((∫ x, smearedPotential χ η (x - w) ∂smearedCharge χ a α) -
        ∫ x, smearedPotential χ η (x - w) ∂smearedCharge χ b α) +
      ((∫ x, smearedPotential χ η (x - w) ∂smearedCharge χ b α) -
        ∫ x, smearedPotential χ η (x - w) ∂smearedCharge χ b α') := by
  rw [integral_shiftedPotential_eq_kernel hχ, integral_shiftedPotential_eq_kernel hχ,
    integral_shiftedPotential_eq_kernel hχ]
  ring

/-- The translation part is bounded by `|a-b| ‖∇f‖∞`, before estimating
radius change (the proof of Lemma 3.9). Both averages have radius `α`. -/
theorem abs_translation_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    {α η : ℝ} (hα : 0 < α) (hη : 0 < η) (a b w : ℂ) :
    |(∫ x, smearedPotential χ η (x - w) ∂smearedCharge χ a α) -
      ∫ x, smearedPotential χ η (x - w) ∂smearedCharge χ b α| ≤
      Real.sqrt (Real.pi * M) * ‖a - b‖ / η := by
  have := isProbabilityMeasure_smearedCharge hχ 0 hα
  rw [integral_shiftedPotential_eq_kernel hχ, integral_shiftedPotential_eq_kernel hχ,
    twoRadiusKernel_eq_integral_smearedPotential hχ,
    twoRadiusKernel_eq_integral_smearedPotential hχ, ← integral_sub
      (integrable_smearedPotential_comp hχ hη (f := fun x => a - w - x)
        (continuous_const.sub continuous_id) 0 α)
      (integrable_smearedPotential_comp hχ hη (f := fun x => b - w - x)
        (continuous_const.sub continuous_id) 0 α),
    ← Real.norm_eq_abs]
  have hb : ∀ᵐ x ∂smearedCharge χ 0 α,
      ‖smearedPotential χ η (a - w - x) - smearedPotential χ η (b - w - x)‖ ≤
        Real.sqrt (Real.pi * M) / η * ‖a - b‖ :=
    Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      have h := UpperBound.abs_smearedPotential_sub_le hχ hM hη (a - w - x) (b - w - x)
      rwa [show a - w - x - (b - w - x) = a - b by ring] at h
  calc _ ≤ (Real.sqrt (Real.pi * M) / η * ‖a - b‖) *
        (smearedCharge χ 0 α).real Set.univ := norm_integral_le_of_norm_le_const hb
    _ = _ := by rw [probReal_univ, mul_one]; ring

/-- The radius-change part uses Taylor expansion at the same centre `b`
for both radii. Evenness removes both linear terms (the proof of Lemma 3.9). -/
theorem abs_radius_change_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    {α α' η : ℝ} (hα : 0 < α) (hα' : 0 < α') (hη : 0 < η) (b w : ℂ) :
    |(∫ x, smearedPotential χ η (x - w) ∂smearedCharge χ b α) -
      ∫ x, smearedPotential χ η (x - w) ∂smearedCharge χ b α'| ≤
      6 * Real.pi * M * max α α' ^ 2 / η ^ 2 := by
  rw [integral_shiftedPotential_eq_kernel hχ, integral_shiftedPotential_eq_kernel hχ]
  have h1 := abs_twoRadiusKernel_sub_smearedPotential_le_sq hχ hM hα hη (b - w)
  have h2 := abs_twoRadiusKernel_sub_smearedPotential_le_sq hχ hM hα' hη (b - w)
  have hM0 := hχ.nonneg_of_le hM
  have hαm : α ^ 2 ≤ max α α' ^ 2 := pow_le_pow_left₀ hα.le (le_max_left _ _) 2
  have hαm' : α' ^ 2 ≤ max α α' ^ 2 := pow_le_pow_left₀ hα'.le (le_max_right _ _) 2
  calc _ ≤ |twoRadiusKernel χ α η (b - w) - smearedPotential χ η (b - w)| +
        |twoRadiusKernel χ α' η (b - w) - smearedPotential χ η (b - w)| := by
          simpa only [abs_sub_comm (smearedPotential χ η (b - w))] using
            (abs_sub_le (twoRadiusKernel χ α η (b - w)) (smearedPotential χ η (b - w))
              (twoRadiusKernel χ α' η (b - w)))
    _ ≤ 3 * (Real.pi * M / η ^ 2) * α ^ 2 +
        3 * (Real.pi * M / η ^ 2) * α' ^ 2 := add_le_add h1 h2
    _ ≤ 3 * (Real.pi * M / η ^ 2) * max α α' ^ 2 +
        3 * (Real.pi * M / η ^ 2) * max α α' ^ 2 := by gcongr
    _ = _ := by ring

end RouteLocal

end MultipoleBKT

end
