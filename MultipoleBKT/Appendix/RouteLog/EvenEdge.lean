/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.RouteLog.Spatial

/-!
# The logarithmic even-edge integral

See the proof of Lemma A.4. Set `s = min(ρᵢ, ρⱼ)` and `t = max(ρᵢ, ρⱼ)`.
The even-edge profile is a near-disc indicator plus the square of the odd profile
outside that disc. Its integral splits into the near disc, the annulus from `s`
to `t`, and the inverse-fourth-power tail beyond `t`.
-/

@[expose] public section

namespace MultipoleBKT.RouteLog

open MeasureTheory Set
open scoped ENNReal

open scoped Classical in
/-- The radial upper profile of `b̂ᵢⱼ`, including the near edge. -/
noncomputable def evenEdgeProfile (M s t d : ℝ) : ℝ :=
  if d ≤ M * s then 1 else (s * t / (d * max d t)) ^ 2

private theorem lintegral_inverse_fourth_tail {t : ℝ} (ht : 0 < t) :
    ∫⁻ z in {z : ℂ | t < ‖z‖}, ENNReal.ofReal (‖z‖ ^ (-4 : ℝ)) ≤
      ENNReal.ofReal (Real.pi / t ^ 2) := by
  have hb := GeneralExpansion.lintegral_tail_max_rpow_le
    (lam := t) (e := -4) ht (by norm_num) (le_refl t)
  have heq :
      (∫⁻ z in {z : ℂ | ‖z‖ ∈ Ioi t}, ENNReal.ofReal (max ‖z‖ t ^ (-4 : ℝ))) =
      ∫⁻ z in {z : ℂ | t < ‖z‖}, ENNReal.ofReal (‖z‖ ^ (-4 : ℝ)) := by
    apply setLIntegral_congr_fun (measurable_norm measurableSet_Ioi)
    intro z hz
    dsimp only
    rw [max_eq_left hz.le]
  rw [heq] at hb
  convert hb using 1
  norm_num [Real.rpow_neg, Real.rpow_two]
  ring_nf

/-- The even edge has the written logarithmic bound `C s² (1 + log(t/s))`.
The explicit coefficient `π (M² + 3)` is uniform in the two radii. -/
theorem lintegral_evenEdgeProfile_le {M s t : ℝ} (hM : 1 ≤ M) (hs : 0 < s) (hst : s ≤ t) :
    ∫⁻ z : ℂ, ENNReal.ofReal (evenEdgeProfile M s t ‖z‖) ≤
      ENNReal.ofReal (Real.pi * (M ^ 2 + 3) * s ^ 2 * (1 + Real.log (t / s))) := by
  have ht : 0 < t := hs.trans_le hst
  have hMs : s ≤ M * s := by nlinarith
  let A : ℂ → ℝ≥0∞ := (Metric.closedBall (0 : ℂ) (M * s)).indicator 1
  let B : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (s ^ 2) *
    {z : ℂ | ‖z‖ ∈ Ioc s t}.indicator (fun z => ENNReal.ofReal ((‖z‖ ^ 2)⁻¹)) z
  let D : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (s ^ 2 * t ^ 2) *
    {z : ℂ | t < ‖z‖}.indicator (fun z => ENNReal.ofReal (‖z‖ ^ (-4 : ℝ))) z
  have hA : Measurable A := measurable_one.indicator Metric.isClosed_closedBall.measurableSet
  have hBs : MeasurableSet {z : ℂ | ‖z‖ ∈ Ioc s t} := measurable_norm measurableSet_Ioc
  have hDs : MeasurableSet {z : ℂ | t < ‖z‖} := measurable_norm measurableSet_Ioi
  have hB : Measurable B := by dsimp [B]; fun_prop
  have hD : Measurable D := by dsimp [D]; fun_prop
  have hpoint (z : ℂ) : ENNReal.ofReal (evenEdgeProfile M s t ‖z‖) ≤ A z + B z + D z := by
    unfold evenEdgeProfile
    by_cases hnear : ‖z‖ ≤ M * s
    · rw [ite_eq_left hnear]
      have hz : z ∈ Metric.closedBall (0 : ℂ) (M * s) := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hnear
      have he : A z = 1 := indicator_of_mem hz _
      rw [he, ENNReal.ofReal_one]
      exact (le_add_right le_rfl).trans (le_add_right le_rfl)
    · rw [ite_eq_right hnear]
      have hz : 0 < ‖z‖ := hs.trans (hMs.trans_lt (lt_of_not_ge hnear))
      by_cases hzt : ‖z‖ ≤ t
      · have hmem : ‖z‖ ∈ Ioc s t := ⟨hMs.trans_lt (lt_of_not_ge hnear), hzt⟩
        have he : B z = ENNReal.ofReal (s ^ 2 * (‖z‖ ^ 2)⁻¹) := by
          dsimp [B]
          rw [indicator_of_mem (show z ∈ {z : ℂ | ‖z‖ ∈ Ioc s t} from hmem),
            ← ENNReal.ofReal_mul (sq_nonneg _)]
        have heq : (s * t / (‖z‖ * max ‖z‖ t)) ^ 2 = s ^ 2 * (‖z‖ ^ 2)⁻¹ := by
          rw [max_eq_right hzt]
          field_simp
        rw [heq]
        exact (le_add_left (le_of_eq he.symm)).trans (le_add_right le_rfl)
      · have hmem : t < ‖z‖ := lt_of_not_ge hzt
        have he : D z = ENNReal.ofReal (s ^ 2 * t ^ 2 * ‖z‖ ^ (-4 : ℝ)) := by
          dsimp [D]
          rw [indicator_of_mem (show z ∈ {z : ℂ | t < ‖z‖} from hmem),
            ← ENNReal.ofReal_mul (by positivity)]
        have heq : (s * t / (‖z‖ * max ‖z‖ t)) ^ 2 = s ^ 2 * t ^ 2 * ‖z‖ ^ (-4 : ℝ) := by
          rw [max_eq_left hmem.le, Real.rpow_neg hz.le, Real.rpow_ofNat]
          field_simp
        rw [heq]
        exact le_add_left (le_of_eq he.symm)
  have hIA : ∫⁻ z, A z = ENNReal.ofReal (Real.pi * M ^ 2 * s ^ 2) := by
    dsimp [A]
    rw [lintegral_indicator Metric.isClosed_closedBall.measurableSet]
    simp only [Pi.one_apply]
    rw [setLIntegral_one, Complex.volume_closedBall]
    rw [← ENNReal.ofReal_pow (by positivity)]
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have hIB : ∫⁻ z, B z = ENNReal.ofReal (2 * Real.pi * s ^ 2 * Real.log (t / s)) := by
    dsimp [B]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_indicator hBs, lintegral_planar_annular_inverse_square hs hst,
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    ring
  have hID : ∫⁻ z, D z ≤ ENNReal.ofReal (Real.pi * s ^ 2) := by
    dsimp [D]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator hDs]
    calc
      _ ≤ ENNReal.ofReal (s ^ 2 * t ^ 2) * ENNReal.ofReal (Real.pi / t ^ 2) := by
        gcongr
        exact lintegral_inverse_fourth_tail ht
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
  have hlog : 0 ≤ Real.log (t / s) := Real.log_nonneg ((one_le_div hs).2 hst)
  calc
    _ ≤ ∫⁻ z, A z + B z + D z := lintegral_mono hpoint
    _ = (∫⁻ z, A z) + (∫⁻ z, B z) + ∫⁻ z, D z := by
      rw [lintegral_add_left (show Measurable (fun z => A z + B z) from hA.add hB) _,
        lintegral_add_left hA _]
    _ ≤ ENNReal.ofReal (Real.pi * M ^ 2 * s ^ 2) +
        ENNReal.ofReal (2 * Real.pi * s ^ 2 * Real.log (t / s)) +
        ENNReal.ofReal (Real.pi * s ^ 2) := by rw [hIA, hIB]; gcongr
    _ ≤ _ := by
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ Real.pi * M ^ 2 * s ^ 2) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_nonneg (sq_nonneg M) hlog, Real.pi_pos,
        mul_nonneg (sq_nonneg s) hlog, mul_nonneg (Real.pi_pos.le) (sq_nonneg s)]

end MultipoleBKT.RouteLog

end
