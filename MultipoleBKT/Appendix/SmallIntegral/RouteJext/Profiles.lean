/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.EndpointIntegration
public import MultipoleBKT.Appendix.RouteLog.Spatial

/-!
# The cutoff tree factors of J_ext

See Lemma A.4. Odd edges are integrated on
`R_* < d ≤ 17h`. The common translation is integrated before the independent
edge coordinates, with its logarithmic bound left as a factor.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJext

open MeasureTheory Set Finset Limits RouteJ
open scoped Classical ENNReal

/-- The inverse-square profile with both cutoffs. -/
noncomputable def oddProfile (a h d : ℝ) : ℝ :=
  (Ioc a (17 * h)).indicator (fun d => (d ^ 2)⁻¹) d

theorem measurable_oddProfile (a h : ℝ) : Measurable (oddProfile a h) := by
  unfold oddProfile
  exact Measurable.indicator (by fun_prop) measurableSet_Ioc

/-- The odd annulus contributes its logarithm without a distributed tail. -/
theorem lintegral_oddProfile {a h : ℝ} (ha : 0 < a) (hah : a ≤ h) :
    (∫⁻ z : ℂ, ENNReal.ofReal (oddProfile a h ‖z‖)) =
      ENNReal.ofReal (2 * Real.pi * Real.log (17 * h / a)) := by
  have hs : MeasurableSet {z : ℂ | ‖z‖ ∈ Ioc a (17 * h)} := measurable_norm measurableSet_Ioc
  have he : (fun z : ℂ => ENNReal.ofReal (oddProfile a h ‖z‖)) =
      {z : ℂ | ‖z‖ ∈ Ioc a (17 * h)}.indicator
        (fun z => ENNReal.ofReal ((‖z‖ ^ 2)⁻¹)) := by
    funext z
    unfold oddProfile
    by_cases hz : ‖z‖ ∈ Ioc a (17 * h)
    · rw [indicator_of_mem hz, indicator_of_mem (show z ∈ {z : ℂ | ‖z‖ ∈ Ioc a (17 * h)} from hz)]
    · rw [indicator_of_notMem hz, indicator_of_notMem (show z ∉ {z : ℂ | ‖z‖ ∈ Ioc a (17 * h)} from hz), ENNReal.ofReal_zero]
  rw [he, lintegral_indicator hs]
  exact MultipoleBKT.RouteLog.lintegral_planar_annular_inverse_square ha (by linarith)

/-- Root first, then the independent tree coordinates. The root weight can
include the external gain and its box indicator. -/
theorem lintegral_endpoint_product_le {V : Type*} [Fintype V] [DecidableEq V]
    (root : V) (par : V → V) (depth : V → ℕ)
    (hdepth : ∀ i, i ≠ root → depth (par i) < depth i) (u : V → ℂ)
    (H : ℂ → ℝ≥0∞) (hH : Measurable H)
    (f : {i // i ≠ root} → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : V → ℂ, H (x root) * ∏ i : {i // i ≠ root},
      f i (dipoleDist (ofPosVec x u i) (ofPosVec x u (par i)))) ≤
      (4 : ℝ≥0∞) ^ Fintype.card {i // i ≠ root} *
        ((∫⁻ t, H t) * ∏ i : {i // i ≠ root}, ∫⁻ z : ℂ, f i ‖z‖) := by
  let Φ (d : {i // i ≠ root} → ℝ) := ∏ i, f i (d i)
  have hΦ : Measurable Φ := Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
  have hs := lintegral_endpoint_sectors root par depth hdepth u H hH Φ hΦ
  have hp : (∫⁻ z : V → ℂ, H (z root) * Φ (fun i => ‖z i‖)) =
      (∫⁻ t, H t) * ∏ i : {i // i ≠ root}, ∫⁻ z : ℂ, f i ‖z‖ := by
    rw [lintegral_root_coordinates root H hH
      (fun z : {i // i ≠ root} → ℂ => Φ (fun i => ‖z i‖))
      (hΦ.comp (show Measurable (fun z : {i // i ≠ root} → ℂ => fun i => ‖z i‖) by fun_prop))]
    congr 1
    rw [volume_pi]
    exact lintegral_pi_prod _ _ (fun i => (hf i).comp measurable_norm)
  exact hs.trans_eq (congrArg ((4 : ℝ≥0∞) ^ Fintype.card {i // i ≠ root} * ·) hp)

end MultipoleBKT.SmallIntegral.RouteJext

end
