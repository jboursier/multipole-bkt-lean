/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Energy.RouteGreen.WeakDerivative
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Translation and scaling of the displayed Green problem

The discussion after (3.19) in the paper uses `G₁((x-z)/τ,(y-z)/τ)` on `B(z,τ)`.
Its gradient scales by `τ⁻¹` and its compensating density by `τ⁻²`.
The source equation below is the first order distributional formulation,
tested on compactly supported `C¹` functions inside the disc.
-/

@[expose] public section

open MeasureTheory Metric Set InnerProductSpace

namespace MultipoleBKT.RouteGreen

/-- The displayed kernel transported to a disc, as in the discussion after (3.19). -/
noncomputable def discKernel (z : ℂ) (τ : ℝ) (x y : ℂ) : ℝ :=
  kernel (τ⁻¹ • (x - z)) (τ⁻¹ • (y - z))

/-- The gradient transported to a disc, as in the discussion after (3.19). -/
noncomputable def discField (z : ℂ) (τ : ℝ) (x y : ℂ) : ℂ :=
  τ⁻¹ • field (τ⁻¹ • (x - z)) (τ⁻¹ • (y - z))

/-- The uniform probability density in the disc, as in the Green problem
preceding (3.19), rescaled for `τ > 0`. -/
noncomputable def discDensity (τ : ℝ) : ℝ := (Real.pi * τ ^ 2)⁻¹

/-- Evaluating the transported kernel in unit coordinates, as in the discussion after (3.19). -/
theorem discKernel_at_scale {τ : ℝ} (hτ : 0 < τ) (z u v : ℂ) :
    discKernel z τ (z + τ • u) (z + τ • v) = kernel u v := by
  simp [discKernel, hτ.ne']

/-- The gradient is `τ⁻¹` times the unit gradient, as in the discussion after (3.19). -/
theorem discField_at_scale {τ : ℝ} (hτ : 0 < τ) (z u v : ℂ) :
    discField z τ (z + τ • u) (z + τ • v) = τ⁻¹ • field u v := by
  simp [discField, hτ.ne']

/-- A source at the center uses the displayed logarithm directly,
as in the discussion after (3.19). -/
theorem discKernel_center (z x : ℂ) (τ : ℝ) :
    discKernel z τ x z = -Real.log ‖τ⁻¹ • (x - z)‖ +
      ‖τ⁻¹ • (x - z)‖ ^ 2 / 2 := by
  simp only [discKernel, sub_self, smul_zero, kernel_center]

private theorem norm_rescale (z x : ℂ) {τ : ℝ} (hτ : 0 < τ) :
    ‖τ⁻¹ • (x - z)‖ = ‖x - z‖ / τ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hτ)]
  ring

/-- Differentiating the rescaled potential introduces the factor `τ⁻¹`,
as in the scaling step after (3.22). -/
theorem hasFDerivAt_discKernel {z x y : ℂ} {τ : ℝ} (hτ : 0 < τ)
    (hx : ‖x - z‖ ≤ τ) (hy : ‖y - z‖ < τ) (hxy : x ≠ y) :
    HasFDerivAt (fun w => discKernel z τ w y)
      (toDual ℝ ℂ (discField z τ x y)) x := by
  have hx' : ‖τ⁻¹ • (x - z)‖ ≤ 1 := by
    rw [norm_rescale z x hτ, div_le_one hτ]
    exact hx
  have hy' : ‖τ⁻¹ • (y - z)‖ < 1 := by
    rw [norm_rescale z y hτ, div_lt_one hτ]
    exact hy
  have hxy' : τ⁻¹ • (x - z) ≠ τ⁻¹ • (y - z) := by
    intro h
    apply hxy
    exact sub_left_injective ((smul_right_injective ℂ (inv_ne_zero hτ.ne')) h)
  have h := (hasFDerivAt_kernel hx' hy' hxy').comp x
    (((hasFDerivAt_id x).sub_const z).const_smul τ⁻¹)
  apply h.congr_fderiv
  ext v
  simp only [discField, map_smul, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.id_apply, toDual_apply_apply]

/-- The Neumann identity scales to every disc. The outward unit normal
is `τ⁻¹ • (x-z)`, as in the discussion after (3.19). -/
theorem disc_boundary {z x y : ℂ} {τ : ℝ} (hτ : 0 < τ)
    (hx : ‖x - z‖ = τ) (hy : ‖y - z‖ < τ) :
    inner ℝ (τ⁻¹ • (x - z)) (discField z τ x y) = 0 := by
  have hx' : ‖τ⁻¹ • (x - z)‖ = 1 := by
    rw [norm_rescale z x hτ, hx, div_self hτ.ne']
  have hy' : ‖τ⁻¹ • (y - z)‖ < 1 := by
    rw [norm_rescale z y hτ, div_lt_one hτ]
    exact hy
  rw [discField, real_inner_smul_right, boundary hx' hy', mul_zero]

/-- The rescaled potential itself has zero normal derivative,
as in the discussion after (3.19). -/
theorem disc_normal_derivative {z x y : ℂ} {τ : ℝ} (hτ : 0 < τ)
    (hx : ‖x - z‖ = τ) (hy : ‖y - z‖ < τ) :
    fderiv ℝ (fun w => discKernel z τ w y) x (τ⁻¹ • (x - z)) = 0 := by
  have hxy : x ≠ y := by intro h; rw [← h, hx] at hy; exact lt_irrefl _ hy
  rw [(hasFDerivAt_discKernel hτ hx.le hy hxy).fderiv, toDual_apply_apply,
    real_inner_comm, disc_boundary hτ hx hy]

/-- The rescaled density has mass one, as in the discussion after (3.19). -/
theorem integral_discDensity {τ : ℝ} (hτ : 0 < τ) (z : ℂ) :
    ∫ _ : ℂ in ball z τ, discDensity τ = 1 := by
  rw [setIntegral_const, smul_eq_mul, volume_real_ball_complex z hτ.le]
  exact mul_inv_cancel₀ (mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 hτ.ne'))

private theorem integral_translate_scale (f : ℂ → ℝ) (z : ℂ) {τ : ℝ}
    (hτ : 0 < τ) :
    ∫ u, f (z + τ • u) = (τ ^ 2)⁻¹ * ∫ w, f w := by
  rw [Measure.integral_comp_smul_of_nonneg volume (fun u => f (z + u)) τ
    (hR := hτ.le), Complex.finrank_real_complex, smul_eq_mul,
    integral_add_left_eq_self]

/-- The weak gradient identity also scales across the singularity,
as in the discussion after (3.19). -/
theorem disc_weak_derivative {z y : ℂ} {τ : ℝ} (hτ : 0 < τ) (hy : ‖y - z‖ < τ)
    {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ)
    (hs : tsupport ξ ⊆ ball z τ) (v : ℂ) :
    ∫ w, discKernel z τ w y * fderiv ℝ ξ w v =
      -∫ w, inner ℝ (discField z τ w y) v * ξ w := by
  let η : ℂ → ℝ := fun u => ξ (z + τ • u)
  have hη : ContDiff ℝ 1 η := hξ.comp (contDiff_const.add (contDiff_id.const_smul τ))
  let e : ℂ ≃ₜ ℂ := (Homeomorph.smul (isUnit_iff_ne_zero.2 hτ.ne').unit).trans
    (Homeomorph.addLeft z)
  have hηc : HasCompactSupport η := hc.comp_isClosedEmbedding e.isClosedEmbedding
  have hηs : tsupport η ⊆ ball 0 1 := by
    intro u hu
    have hmem := hs (tsupport_comp_subset_preimage ξ e.continuous hu)
    change z + τ • u ∈ ball z τ at hmem
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hτ] at hmem
    rw [mem_ball_zero_iff]
    nlinarith
  have hy' : ‖τ⁻¹ • (y - z)‖ < 1 := by
    rw [norm_rescale z y hτ, div_lt_one hτ]
    exact hy
  have hd (u : ℂ) : fderiv ℝ η u v = τ * fderiv ℝ ξ (z + τ • u) v := by
    have h := (hξ.differentiable one_ne_zero (z + τ • u)).hasFDerivAt.comp u
      ((hasFDerivAt_const z u).add ((hasFDerivAt_id u).const_smul τ))
    change fderiv ℝ (ξ ∘ ((fun _ : ℂ => z) + τ • id)) u v = _
    rw [h.fderiv]
    simp
  have ht := weak_derivative hy' hη hηc hηs v
  simp_rw [hd] at ht
  have hl := integral_translate_scale
    (fun w => discKernel z τ w y * fderiv ℝ ξ w v) z hτ
  have hr := integral_translate_scale
    (fun w => inner ℝ (discField z τ w y) v * ξ w) z hτ
  have harg (u : ℂ) : τ⁻¹ • (z + τ • u - z) = u := by simp [hτ.ne']
  conv_lhs at hl => simp only [discKernel, harg]
  conv_lhs at hr =>
    simp only [discField, harg, real_inner_smul_left, mul_assoc, integral_const_mul]
  simp_rw [mul_left_comm (kernel _ _) τ, integral_const_mul] at ht
  change τ * (∫ u, kernel u (τ⁻¹ • (y - z)) * fderiv ℝ ξ (z + τ • u) v) =
    -(∫ u, inner ℝ (field u (τ⁻¹ • (y - z))) v * ξ (z + τ • u)) at ht
  field_simp [hτ.ne'] at hl hr
  simp only [one_div] at hl hr
  linear_combination τ * ht - hl - hr

/-- The complete distributional source equation after scaling, as in the discussion after (3.19). Testing the negative divergence of `discField` gives
`2π(δ_y - 1/(πτ²))`. The pole is included in this identity. -/
theorem disc_source {z y : ℂ} {τ : ℝ} (hτ : 0 < τ) (hy : ‖y - z‖ < τ)
    {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ)
    (hs : tsupport ξ ⊆ ball z τ) :
    ∫ w, fderiv ℝ ξ w (discField z τ w y) =
      2 * Real.pi * (ξ y - ∫ w, discDensity τ * ξ w) := by
  let η : ℂ → ℝ := fun u => ξ (z + τ • u)
  have hη : ContDiff ℝ 1 η := hξ.comp (contDiff_const.add (contDiff_id.const_smul τ))
  let e : ℂ ≃ₜ ℂ := (Homeomorph.smul (isUnit_iff_ne_zero.2 hτ.ne').unit).trans
    (Homeomorph.addLeft z)
  have he (u : ℂ) : e u = z + τ • u := rfl
  have hηc : HasCompactSupport η := hc.comp_isClosedEmbedding e.isClosedEmbedding
  have hηs : tsupport η ⊆ ball 0 1 := by
    intro u hu
    have hmem := hs (tsupport_comp_subset_preimage ξ e.continuous hu)
    rw [he, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hτ] at hmem
    rw [mem_ball_zero_iff]
    nlinarith
  have hy' : ‖τ⁻¹ • (y - z)‖ < 1 := by
    rw [norm_rescale z y hτ, div_lt_one hτ]
    exact hy
  have hd (u v : ℂ) : fderiv ℝ η u v =
      τ * fderiv ℝ ξ (z + τ • u) v := by
    have h := (hξ.differentiable one_ne_zero (z + τ • u)).hasFDerivAt.comp u
      ((hasFDerivAt_const z u).add ((hasFDerivAt_id u).const_smul τ))
    change fderiv ℝ (ξ ∘ ((fun _ : ℂ => z) + τ • id)) u v = _
    rw [h.fderiv]
    simp
  have ht := source hy' hη hηc hηs
  have hleft := integral_translate_scale
    (fun w => fderiv ℝ ξ w (discField z τ w y)) z hτ
  have harg (u : ℂ) : τ⁻¹ • (z + τ • u - z) = u := by
    simp [hτ.ne']
  simp only [discField, harg, map_smul, smul_eq_mul] at hleft
  simp_rw [hd] at ht
  rw [integral_const_mul] at ht hleft
  have hηint : ∫ u, η u = (τ ^ 2)⁻¹ * ∫ w, ξ w :=
    integral_translate_scale ξ z hτ
  rw [integral_const_mul, hηint] at ht
  have hyarg : η (τ⁻¹ • (y - z)) = ξ y := by
    simp [η, hτ.ne']
  rw [hyarg] at ht
  rw [integral_const_mul]
  unfold density at ht
  unfold discDensity
  simp only [discField, map_smul, smul_eq_mul, integral_const_mul]
  field_simp [hτ.ne', Real.pi_ne_zero] at ht hleft ⊢
  rw [integral_div] at hleft
  field_simp [hτ.ne'] at hleft
  linear_combination ht - τ * hleft

end MultipoleBKT.RouteGreen
