/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.RouteLog.Spatial

/-!
# Logarithmic common-translation estimates

See (A.41). The root sees a finite set of translated
bad endpoints. The cap supplies the area term. Each endpoint supplies one
truncated inverse-square disc integral, with its logarithm retained.
-/

@[expose] public section

namespace MultipoleBKT.RouteLog

open MeasureTheory Set Finset
open scoped ENNReal

/-- The capped inverse-square kernel for a finite family of endpoints.
It is the maximum of the cap contribution and the individual regularized kernels. -/
noncomputable def cappedInverseSquare (P : Finset ℂ) (R h : ℝ) (z : ℂ) : ℝ≥0∞ :=
  max (ENNReal.ofReal ((h ^ 2)⁻¹))
    (P.sup fun p => ENNReal.ofReal ((max ‖z - p‖ R ^ 2)⁻¹))

private theorem lintegral_translated_truncated {R h : ℝ} (hR : 0 < R) (hRh : R ≤ h) (p : ℂ) :
    ∫⁻ z : ℂ, {z : ℂ | ‖z - p‖ ≤ h}.indicator
      (fun z => ENNReal.ofReal ((max ‖z - p‖ R ^ 2)⁻¹)) z =
      ENNReal.ofReal (2 * Real.pi * (1 / 2 + Real.log (h / R))) := by
  have he : (fun z : ℂ => {z : ℂ | ‖z - p‖ ≤ h}.indicator
      (fun z => ENNReal.ofReal ((max ‖z - p‖ R ^ 2)⁻¹)) z) =
      fun z : ℂ => {z : ℂ | ‖z‖ ≤ h}.indicator
        (fun z => ENNReal.ofReal ((max ‖z‖ R ^ 2)⁻¹)) (z - p) := by
    funext z
    simp only [indicator_apply, Set.mem_ofPred_eq]
  rw [he, lintegral_sub_right_eq_self]
  have hs : MeasurableSet {z : ℂ | ‖z‖ ≤ h} := measurable_norm measurableSet_Iic
  rw [lintegral_indicator hs]
  exact lintegral_planar_truncated_inverse_square hR hRh

/-- The bad-root area estimate for any finite family of endpoints.
For dipoles, the endpoint count is at most twice the number of bad dipoles. -/
theorem bad_endpoint_area_le (P : Finset ℂ) {R : ℝ} (hR : 0 ≤ R) :
    volume (⋃ p ∈ P, Metric.ball p R) ≤ P.card * ENNReal.ofReal (Real.pi * R ^ 2) := by
  calc
    _ ≤ ∑ p ∈ P, volume (Metric.ball p R) := measure_biUnion_finset_le P _
    _ = _ := by
      simp only [Complex.volume_ball, Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [← ENNReal.ofReal_pow hR, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
        ← ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      ring

/-- Root inverse-square integration over any region, uniformly in the endpoints. -/
theorem lintegral_cappedInverseSquare_le (P : Finset ℂ) {R h : ℝ}
    (hR : 0 < R) (hRh : R ≤ h) (D : Set ℂ) :
    ∫⁻ z in D, cappedInverseSquare P R h z ≤
      ENNReal.ofReal ((h ^ 2)⁻¹) * volume D +
        P.card * ENNReal.ofReal (2 * Real.pi * (1 / 2 + Real.log (h / R))) := by
  have hh := hR.trans_le hRh
  let K : ℂ → ℂ → ℝ≥0∞ := fun p z => {z : ℂ | ‖z - p‖ ≤ h}.indicator
    (fun z => ENNReal.ofReal ((max ‖z - p‖ R ^ 2)⁻¹)) z
  have hKm (p : ℂ) : Measurable (K p) := by
    have hs : MeasurableSet {z : ℂ | ‖z - p‖ ≤ h} :=
      (measurable_norm.comp (measurable_id.sub_const p)) measurableSet_Iic
    dsimp [K]
    fun_prop
  have hpoint (z : ℂ) : cappedInverseSquare P R h z ≤
      ENNReal.ofReal ((h ^ 2)⁻¹) + ∑ p ∈ P, K p z := by
    apply max_le
    · exact le_add_right le_rfl
    · apply Finset.sup_le
      intro p hp
      by_cases hz : ‖z - p‖ ≤ h
      · have he : K p z = ENNReal.ofReal ((max ‖z - p‖ R ^ 2)⁻¹) := by
          dsimp [K]
          rw [indicator_of_mem (show z ∈ {z : ℂ | ‖z - p‖ ≤ h} from hz)]
        have hi := Finset.single_le_sum (f := fun p => K p z) (fun _ _ => bot_le) hp
        exact (le_of_eq he.symm).trans (hi.trans (le_add_left le_rfl))
      · have hzh : h ≤ max ‖z - p‖ R := (le_of_not_ge hz).trans (le_max_left _ _)
        have hi : (max ‖z - p‖ R ^ 2)⁻¹ ≤ (h ^ 2)⁻¹ := by
          apply inv_anti₀ (sq_pos_of_pos hh)
          exact pow_le_pow_left₀ hh.le hzh 2
        exact (ENNReal.ofReal_le_ofReal hi).trans (le_add_right le_rfl)
  calc
    _ ≤ ∫⁻ z in D, ENNReal.ofReal ((h ^ 2)⁻¹) + ∑ p ∈ P, K p z := lintegral_mono hpoint
    _ = ENNReal.ofReal ((h ^ 2)⁻¹) * volume D + ∑ p ∈ P, ∫⁻ z in D, K p z := by
      rw [lintegral_add_left measurable_const _, setLIntegral_const, mul_comm]
      rw [lintegral_finsetSum P (fun p _ => hKm p)]
    _ ≤ ENNReal.ofReal ((h ^ 2)⁻¹) * volume D +
        ∑ p ∈ P, ∫⁻ z, K p z := by
      gcongr
      exact Measure.restrict_le_self
    _ = _ := by
      simp_rw [show ∀ p, ∫⁻ z, K p z =
        ENNReal.ofReal (2 * Real.pi * (1 / 2 + Real.log (h / R))) from
          fun p => lintegral_translated_truncated hR hRh p]
      simp

/-- Common translation with the quadratic tail, before the radial cancellation.
Multiplication by `R²` produces exactly the factor cancelled at (A.25). -/
theorem lintegral_root_quadratic_tail_le (P : Finset ℂ) {R h : ℝ}
    (hR : 0 < R) (hRh : R ≤ h) (D : Set ℂ) :
    ∫⁻ z in D, ENNReal.ofReal (R ^ 2) * cappedInverseSquare P R h z ≤
      ENNReal.ofReal (R ^ 2 / h ^ 2) * volume D +
        P.card * ENNReal.ofReal (2 * Real.pi * R ^ 2 * (1 / 2 + Real.log (h / R))) := by
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    _ ≤ ENNReal.ofReal (R ^ 2) *
        (ENNReal.ofReal ((h ^ 2)⁻¹) * volume D +
          P.card * ENNReal.ofReal (2 * Real.pi * (1 / 2 + Real.log (h / R)))) := by
      gcongr
      exact lintegral_cappedInverseSquare_le P hR hRh D
    _ = _ := by
      rw [mul_add, ← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _)]
      simp only [div_eq_mul_inv]
      congr 1
      rw [mul_left_comm, ← ENNReal.ofReal_mul (sq_nonneg _)]
      congr 2
      ring

end MultipoleBKT.RouteLog

end
