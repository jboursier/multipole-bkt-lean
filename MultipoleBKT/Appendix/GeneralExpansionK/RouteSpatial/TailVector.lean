/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.TailRadial
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.VectorRadial

/-!
# The vector radial display in case F

See Step 4 of
the proof of Lemma A.7. The largest dipole vector is
outside the cutoff disc. Polar coordinates identify its ordered vector
integral with the logarithmic scalar family, including all inner cores.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset Limits SmallIntegral.RouteJ
open scoped ENNReal

/-- Exact polar reduction for the ordered vector tail. -/
theorem orderedVectorTail_eq (β : ℝ) {lam h : ℝ} (hlam : 0 < lam) (hlh : lam ≤ h) (k q : ℕ) :
    (∫⁻ v in {v : ℂ | h < ‖v‖}, ENNReal.ofReal (rho lam v ^ (-β)) *
      innerVector β lam k q ‖v‖) =
        ENNReal.ofReal (2 * Real.pi) ^ (k + 2) * orderedTail β lam h k q := by
  have hh := hlam.trans_le hlh
  simp_rw [innerVector_eq]
  let F : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (max u lam ^ (-β)) * innerRadial β lam k q u
  have hF : Measurable F := by
    have hm := measurable_innerRadial β lam k q
    fun_prop
  have heq (v : ℂ) : ENNReal.ofReal (rho lam v ^ (-β)) *
      (ENNReal.ofReal (2 * Real.pi) ^ (k + 1) * innerRadial β lam k q ‖v‖) =
      ENNReal.ofReal (2 * Real.pi) ^ (k + 1) * F ‖v‖ := by
    unfold F rho
    ring
  simp_rw [heq]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  have hp := TwoComponentCoulomb.lintegral_radial_set (Ioi h) measurableSet_Ioi F hF
  change ENNReal.ofReal (2 * Real.pi) ^ (k + 1) *
    (∫⁻ v in {v : ℂ | ‖v‖ ∈ Ioi h}, F ‖v‖) = _
  rw [hp]
  have hint : (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u *
      ((Ioi h).indicator F u * ENNReal.ofReal (2 * Real.pi))) =
        ENNReal.ofReal (2 * Real.pi) * orderedTail β lam h k q := by
    have hpt (u : ℝ) : ENNReal.ofReal u * ((Ioi h).indicator F u * ENNReal.ofReal (2 * Real.pi)) =
        ENNReal.ofReal (2 * Real.pi) * (Ioi h).indicator
          (fun u => ENNReal.ofReal (u ^ (1 - β)) * innerRadial β lam k q u) u := by
      by_cases hu : h < u
      · have hu0 := hh.trans hu
        rw [indicator_of_mem (show u ∈ Ioi h from hu), indicator_of_mem (show u ∈ Ioi h from hu)]
        dsimp only [F]
        rw [max_eq_left (hlh.trans hu.le)]
        simp only [← mul_assoc]
        rw [← ENNReal.ofReal_mul hu0.le]
        have he : u * u ^ (-β) = u ^ (1 - β) := by
          rw [mul_comm, ← Real.rpow_add_one hu0.ne']
          congr 1
          ring
        rw [he]
        ring
      · rw [indicator_of_notMem (show u ∉ Ioi h from hu), indicator_of_notMem (show u ∉ Ioi h from hu)]
        simp
    simp_rw [hpt]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, inter_eq_left.mpr (Ioi_subset_Ioi hh.le)]
    rfl
  rw [hint, ← mul_assoc, ← pow_succ]

/-- The written critical case-F display. For `k+2` radii the retained
logarithmic power is `2(k+2)`, before its final absorption. -/
theorem caseF_four (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      orderedTail 4 lam h k (k + 2) ≤ ENNReal.ofReal
        (C * h ^ (-2 : ℝ) * (1 + Real.log (h / lam)) ^ (2 * (k + 2))) := by
  obtain ⟨C,hC,hb⟩ := orderedTail_four k (k + 2)
  refine ⟨C,hC,fun lam h hlam hlh => (hb lam h hlam hlh).trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  have hh := hlam.trans_le hlh
  have hL : 1 ≤ 1 + Real.log (h / lam) := by
    have := Real.log_nonneg ((one_le_div hlam).2 hlh)
    linarith
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega)) (by positivity)

end MultipoleBKT.ExpansionK.RouteSpatial

end
