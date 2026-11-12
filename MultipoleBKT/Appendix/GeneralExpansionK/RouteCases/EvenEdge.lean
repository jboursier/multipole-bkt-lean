/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.RouteLog.Spatial
public import MultipoleBKT.Appendix.GeneralExpansion.CutoffTail

/-!
# Retaining the marked even edge

See case E,
(A.61) and (A.62) and the omitted even-edge display after (A.63) in Step 3 of the proof of Lemma A.7.
The marked kernel has two endpoint squares. Its integral has the logarithm of
`17 h / max(Rᵢ,Rⱼ)`. It is not replaced by a copy of an odd-edge kernel.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open MeasureTheory Set
open scoped ENNReal

/-- The marked even edge after extracting the inverse screening-radius square. -/
noncomputable def markedEvenKernel (s t d : ℝ) : ℝ :=
  s ^ 2 * t ^ 2 / (d * max d (max s t))

private theorem integral_marked_profile {T H : ℝ} (hT : 0 < T) (hTH : T ≤ H) :
    ∫ a in (0 : ℝ)..H, (max a T)⁻¹ = 1 + Real.log (H / T) := by
  have hH : 0 < H := hT.trans_le hTH
  have hc : Continuous (fun a : ℝ => (max a T)⁻¹) := by
    apply Continuous.inv₀ (continuous_id.max continuous_const)
    intro a
    exact (lt_max_of_lt_right hT).ne'
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 T)
    (hc.intervalIntegrable T H)]
  have hlow : (∫ a in (0 : ℝ)..T, (max a T)⁻¹) = 1 := by
    calc _ = ∫ a in (0 : ℝ)..T, T⁻¹ := intervalIntegral.integral_congr fun a ha => by
                rw [uIcc_of_le hT.le] at ha
                rw [max_eq_right ha.2]
         _ = 1 := by simp [hT.ne']
  have hhigh : (∫ a in T..H, (max a T)⁻¹) = Real.log (H / T) := by
    calc _ = ∫ a in T..H, a / a ^ 2 := intervalIntegral.integral_congr fun a ha => by
                rw [uIcc_of_le hTH] at ha
                have ha0 : a ≠ 0 := (hT.trans_le ha.1).ne'
                rw [max_eq_left ha.1]
                field_simp
         _ = _ := RouteLog.integral_annular_inverse_square hT hH
  rw [hlow, hhigh]

/-- Exact evaluation of the marked even edge in the plane. It retains both
endpoint squares, as required for the two trees obtained by deleting the mark. -/
theorem lintegral_marked_even {s t H : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hH : max s t ≤ H) :
    ∫⁻ z in {z : ℂ | ‖z‖ ≤ H}, ENNReal.ofReal (markedEvenKernel s t ‖z‖) =
      ENNReal.ofReal (2 * Real.pi * s ^ 2 * t ^ 2 * (1 + Real.log (H / max s t))) := by
  let T := max s t
  have hT : 0 < T := hs.trans_le (le_max_left _ _)
  have hH0 : 0 < H := hT.trans_le hH
  have hc : Continuous (fun a : ℝ => (max a T)⁻¹) := by
    apply Continuous.inv₀ (continuous_id.max continuous_const)
    intro a
    exact (lt_max_of_lt_right hT).ne'
  change (∫⁻ z in {z : ℂ | ‖z‖ ∈ Iic H}, _) = _
  rw [TwoComponentCoulomb.lintegral_radial_set (Iic H) measurableSet_Iic
    (fun a => ENNReal.ofReal (markedEvenKernel s t a)) (by unfold markedEvenKernel; fun_prop)]
  have heq : ∀ a ∈ Ioi (0 : ℝ), ENNReal.ofReal a *
      ((Iic H).indicator (fun a => ENNReal.ofReal (markedEvenKernel s t a)) a *
        ENNReal.ofReal (2 * Real.pi)) =
      ENNReal.ofReal (2 * Real.pi * s ^ 2 * t ^ 2) *
        (Ioc 0 H).indicator (fun a => ENNReal.ofReal ((max a T)⁻¹)) a := by
    intro a ha
    have ha0 : 0 < a := ha
    by_cases haH : a ≤ H
    · rw [indicator_of_mem (show a ∈ Iic H from haH),
        indicator_of_mem (show a ∈ Ioc 0 H from ⟨ha, haH⟩),
        ← ENNReal.ofReal_mul (by unfold markedEvenKernel; positivity : 0 ≤ markedEvenKernel s t a),
        ← ENNReal.ofReal_mul ha.le, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      unfold markedEvenKernel
      dsimp only [T]
      field_simp [ha0.ne']
    · rw [indicator_of_notMem (show a ∉ Iic H from haH),
        indicator_of_notMem (show a ∉ Ioc 0 H from fun hx => haH hx.2)]
      simp
  rw [setLIntegral_congr_fun measurableSet_Ioi heq,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.2 Ioc_subset_Ioi_self,
    ← ofReal_integral_eq_lintegral_ofReal (hc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun a ha => by positivity)),
    ← intervalIntegral.integral_of_le hH0.le, integral_marked_profile hT hH,
    ← ENNReal.ofReal_mul (by positivity)]

/-- The literal `17 h` marked-edge estimate (A.62). -/
theorem caseE_edge_integral {s t h : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hsh : s ≤ h) (hth : t ≤ h) :
    ∫⁻ z in {z : ℂ | ‖z‖ ≤ 17 * h}, ENNReal.ofReal (markedEvenKernel s t ‖z‖) ≤
      ENNReal.ofReal (2 * Real.pi * s ^ 2 * t ^ 2 * (1 + Real.log (17 * h / max s t))) := by
  apply le_of_eq (lintegral_marked_even hs ht _)
  have hh : 0 ≤ h := hs.le.trans hsh
  exact (max_le hsh hth).trans (by nlinarith)

/-- A long retained even edge supplies the full quadratic spatial tail.
This is the last omitted-edge display of Step 3. -/
theorem long_even_edge_integral {s t H : ℝ} (hH : 0 < H) :
    ∫⁻ z in {z : ℂ | H < ‖z‖}, ENNReal.ofReal (s ^ 2 * t ^ 2 * ‖z‖ ^ (-4 : ℝ)) ≤
      ENNReal.ofReal (Real.pi * min s t ^ 2 * max s t ^ 2 / H ^ 2) := by
  have htail := GeneralExpansion.lintegral_tail_max_rpow_le (lam := H) (e := -4) hH
    (by norm_num) (le_refl H)
  have heq : (∫⁻ z in {z : ℂ | ‖z‖ ∈ Ioi H}, ENNReal.ofReal (max ‖z‖ H ^ (-4 : ℝ))) =
      ∫⁻ z in {z : ℂ | H < ‖z‖}, ENNReal.ofReal (‖z‖ ^ (-4 : ℝ)) := by
    apply setLIntegral_congr_fun (measurable_norm measurableSet_Ioi)
    intro z hz
    dsimp only
    rw [max_eq_left hz.le]
  rw [heq] at htail
  simp only [show (-4 : ℝ) + 2 = -2 by norm_num, Real.rpow_neg hH.le, Real.rpow_two] at htail
  calc _ = ENNReal.ofReal (s ^ 2 * t ^ 2) *
        ∫⁻ z in {z : ℂ | H < ‖z‖}, ENNReal.ofReal (‖z‖ ^ (-4 : ℝ)) := by
          simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ s ^ 2 * t ^ 2)]
          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
       _ ≤ ENNReal.ofReal (s ^ 2 * t ^ 2) *
          ENNReal.ofReal (2 * Real.pi * ((H ^ 2)⁻¹ / - -2)) := by gcongr
       _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [mul_assoc Real.pi, ← mul_pow (min s t) (max s t), min_mul_max]
          ring

end MultipoleBKT.ExpansionK.RouteCases

end
