/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.RouteFlux.Potential

/-!
# Vanishing inner boundary term for the radial field

See Lemma 3.1 of the paper. On the inner boundary of a punctured domain, the field is of
order radius and the arc length is of order radius. The boundary term
therefore tends to zero quadratically, for every compactly supported test.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped RealInnerProductSpace

namespace MultipoleBKT.RouteHessian

open RouteFlux

variable {χ : ℂ → ℝ} {lam : ℝ}

/-- The circle boundary term for differentiating a field component in direction `v`.
For positive `r`, the arc length cancels the radius in the unit normal. -/
noncomputable def originBoundary (χ : ℂ → ℝ) (lam : ℝ) (ξ : ℂ → ℝ)
    (v w : ℂ) (r : ℝ) : ℝ :=
  ∫ θ in Ioo (-Real.pi) Real.pi,
    ξ (circleMap 0 r θ) * ⟪convolvedField χ 0 lam (circleMap 0 r θ), w⟫ *
      ⟪circleMap 0 r θ, v⟫

/-- The inner boundary term is bounded by a constant times `r²`.
This estimate uses the full field, rather than only its normal component. -/
theorem abs_originBoundary_le (hχ : IsMollifier χ) {M : ℝ} (hM : ∀ x, χ x ≤ M)
    (hlam : 0 < lam) {ξ : ℂ → ℝ} {C : ℝ} (hC : ∀ x, |ξ x| ≤ C)
    (v w : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    |originBoundary χ lam ξ v w r| ≤
      2 * Real.pi * C * (Real.pi * M / lam ^ 2) * ‖w‖ * ‖v‖ * r ^ 2 := by
  have hM0 := hχ.nonneg_of_le hM
  have hC0 : 0 ≤ C := (abs_nonneg (ξ 0)).trans (hC 0)
  have hb (θ : ℝ) :
      ‖ξ (circleMap 0 r θ) * ⟪convolvedField χ 0 lam (circleMap 0 r θ), w⟫ *
        ⟪circleMap 0 r θ, v⟫‖ ≤
          C * (Real.pi * M / lam ^ 2 * r * ‖w‖) * (r * ‖v‖) := by
    have he := norm_convolvedField_le_mul hχ hM hlam (circleMap 0 r θ)
    rw [norm_circleMap_zero, abs_of_nonneg hr] at he
    rw [norm_mul, norm_mul, Real.norm_eq_abs (ξ _)]
    apply mul_le_mul
    · apply mul_le_mul (hC _)
        ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right he (norm_nonneg w)))
        (norm_nonneg _) hC0
    · simpa only [norm_circleMap_zero, abs_of_nonneg hr] using
        norm_inner_le_norm (𝕜 := ℝ) (circleMap 0 r θ) v
    · exact norm_nonneg _
    · positivity
  have hi := norm_setIntegral_le_of_norm_le_const
    (μ := (volume : Measure ℝ)) (s := Ioo (-Real.pi) Real.pi) (C := C * (Real.pi * M / lam ^ 2 * r * ‖w‖) * (r * ‖v‖))
    (f := fun θ => ξ (circleMap 0 r θ) * ⟪convolvedField χ 0 lam (circleMap 0 r θ), w⟫ *
      ⟪circleMap 0 r θ, v⟫) measure_Ioo_lt_top (fun θ _ => hb θ)
  rw [Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])] at hi
  change |originBoundary χ lam ξ v w r| ≤ _
  calc
    |originBoundary χ lam ξ v w r| ≤ _ := hi
    _ = _ := by ring

/-- The puncture contributes no boundary term as its radius tends to zero. -/
theorem tendsto_originBoundary_zero (hχ : IsMollifier χ) (hlam : 0 < lam)
    {ξ : ℂ → ℝ} (hξ : Continuous ξ) (hc : HasCompactSupport ξ) (v w : ℂ) :
    Tendsto (originBoundary χ lam ξ v w) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M, hM⟩ := hχ.exists_bound
  obtain ⟨C, hC⟩ := hξ.bounded_above_of_compact_support hc
  have ht : Tendsto (fun r : ℝ =>
      2 * Real.pi * C * (Real.pi * M / lam ^ 2) * ‖w‖ * ‖v‖ * r ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    have hh : Continuous (fun r : ℝ =>
        2 * Real.pi * C * (Real.pi * M / lam ^ 2) * ‖w‖ * ‖v‖ * r ^ 2) := by fun_prop
    simpa using (hh.tendsto 0).mono_left nhdsWithin_le_nhds
  apply squeeze_zero_norm' _ ht
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact abs_originBoundary_le hχ hM hlam (fun x => by simpa only [Real.norm_eq_abs] using hC x)
    v w hr.le

end MultipoleBKT.RouteHessian

end
