/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.TreeIntegral
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.RootLog
public import MultipoleBKT.Appendix.SmallIntegral.RouteJext.Configuration

/-!
# The normalized spatial trees in cases A through E

See Step 3 of
the proof of Lemma A.7. The odd and even edge sets remain
separate. An optional mark denotes the distinguished even edge of case E.
Both endpoint squares have been left for the two-sided radius allocation.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset SimpleGraph Limits Peeling SmallIntegral
open SmallIntegral.RouteJ SmallIntegral.RouteJext GeneralExpansion
open scoped Classical ENNReal

/-- The edge profile after the radius allocation, including the
distinguished even edge when one is selected. -/
noncomputable def activityProfile {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (A E : Finset (Sym2 W)) (mark : Option (Sym2 W)) (M lam h : ℝ) (u : W → ℂ)
    (e : Sym2 W) (d : ℝ) : ℝ :=
  match mark with
  | none => cutProfile A E M lam h u e d
  | some m => markedCutProfile A E m M lam h u e d

/-- The normalized spatial product on the selected label tree. -/
noncomputable def activityTree {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (M lam h : ℝ) (T : SimpleGraph W)
    (A E : Finset (Sym2 W)) (mark : Option (Sym2 W)) (c : W → ℂ × ℂ) : ℝ≥0∞ := by
  classical
  exact ∏ e ∈ T.edgeFinset, ENNReal.ofReal (activityProfile A E mark M lam h (vectors c) e (dipoleDistOn c e))

theorem measurable_activityTree {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (M lam h : ℝ) (T : SimpleGraph W) [DecidableRel T.Adj]
    (A E : Finset (Sym2 W)) (mark : Option (Sym2 W)) :
    Measurable (activityTree M lam h T A E mark) := by
  unfold activityTree
  apply Finset.measurable_prod
  intro e _
  have hd : Measurable (fun c : W → ℂ × ℂ => dipoleDistOn c e) := by
    induction e using Sym2.ind with
    | h i j => exact measurable_dipoleDist.comp (show Measurable (fun c : W → ℂ × ℂ => (c i, c j)) by fun_prop)
  have hcut : Measurable fun c : W → ℂ × ℂ =>
      ENNReal.ofReal (cutProfile A E M lam h (vectors c) e (dipoleDistOn c e)) := by
    simp_rw [cutProfile_of_config]
    split_ifs
    · unfold oddProfile
      exact Measurable.ennreal_ofReal (Measurable.ite
        ((measurableSet_lt (measurable_minRad lam) hd).inter (measurableSet_le hd measurable_const))
        (hd.pow_const 2).inv measurable_const)
    · induction e using Sym2.ind with
      | h i j =>
        simp only [edgeProfile_mk]
        have hd : Measurable (fun c : W → ℂ × ℂ => dipoleDist (c i) (c j)) :=
          measurable_dipoleDist.comp (show Measurable (fun c : W → ℂ × ℂ => (c i, c j)) by fun_prop)
        unfold spatialProfile MultipoleBKT.RouteLog.evenEdgeProfile
        have hi : Measurable (fun c : W → ℂ × ℂ => rhoD lam (c i)) :=
          (measurable_rhoD lam).comp (measurable_pi_apply i)
        have hj : Measurable (fun c : W → ℂ × ℂ => rhoD lam (c j)) :=
          (measurable_rhoD lam).comp (measurable_pi_apply j)
        apply Measurable.ennreal_ofReal
        split_ifs <;> apply Measurable.div _ ((hi.min hj).pow_const 2) <;>
          exact Measurable.ite (measurableSet_le hd (measurable_const.mul (hi.min hj)))
            measurable_const (by fun_prop)
  cases mark with
  | none => exact hcut
  | some m =>
    simp only [activityProfile]
    unfold markedCutProfile
    by_cases he : e = m
    · simp only [ite_eq_left he]
      induction e using Sym2.ind with
      | h i j =>
        unfold markedProfile RouteCases.markedEvenKernel
        apply Measurable.ennreal_ofReal
        apply Measurable.ite (measurableSet_le hd measurable_const)
        · unfold vectors rho
          simp only [edgeMin_mk, radMax_mk, id_eq, dipoleDistOn_mk]
          have hd : Measurable (fun c : W → ℂ × ℂ => dipoleDist (c i) (c j)) :=
            measurable_dipoleDist.comp (show Measurable (fun c : W → ℂ × ℂ => (c i, c j)) by fun_prop)
          fun_prop
        · exact measurable_const
    · simpa only [ite_eq_right he] using hcut

/-- Ordinary and marked trees have the same logarithmic spatial estimate.
The root is integrated first and may contain the actual frozen-root defect. -/
theorem lintegral_activityTree_weighted_le {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    {M lam h : ℝ} (hM : 1 ≤ M) (hlam : 0 < lam) (u : W → ℂ)
    (hu : ∀ i, rho lam (u i) ≤ h) (T : SimpleGraph W) (hT : T.IsTree)
    (A E : Finset (Sym2 W)) (mark : Option (Sym2 W)) (root : W)
    (H : ℂ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ x : W → ℂ, H (x root) * activityTree M lam h T A E mark (ofPosVec x u)) ≤
      (∫⁻ t, H t) * ENNReal.ofReal
        ((4 * Real.pi * (M ^ 2 + 5)) ^ (Fintype.card W - 1) *
          (1 + Real.log (17 * h / minRho lam u)) ^ (Fintype.card W - 1)) := by
  unfold activityTree
  simp_rw [vectors_ofPosVec]
  cases mark with
  | none => exact lintegral_cutTree_weighted_le hM hlam u hu T hT A E root H hH
  | some m => exact lintegral_marked_tree_weighted_le hM hlam u hu T hT A E m root H hH

/-- All radial squares and the cut density, after the radius allocation. -/
noncomputable def activityDensity {W : Type*} [Fintype W]
    (χ : ℂ → ℝ) (β lam h : ℝ) (c : W → ℂ × ℂ) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal (rhoD lam (c i) ^ 2) * ENNReal.ofReal (cutDens χ β lam h (c i))

theorem measurable_activityDensity {W : Type*} [Fintype W] {χ : ℂ → ℝ}
    (hχ : IsMollifier χ) {lam : ℝ} (hlam : 0 < lam) (β h : ℝ) :
    Measurable (activityDensity (W := W) χ β lam h) := by
  unfold activityDensity
  exact Finset.measurable_prod _ fun i _ =>
    (((measurable_rhoD lam).comp (measurable_pi_apply i)).pow_const 2).ennreal_ofReal.mul
      (((measurable_cutDens hχ hlam β h).comp (measurable_pi_apply i)).ennreal_ofReal)

theorem activityDensity_ofPosVec {W : Type*} [Fintype W] {χ : ℂ → ℝ}
    (hχ : IsMollifier χ) (β lam h : ℝ) (x u : W → ℂ) :
    activityDensity χ β lam h (ofPosVec x u) =
      ∏ i, cutWeight χ β lam h (u i) * ENNReal.ofReal (rho lam (u i) ^ 2) := by
  unfold activityDensity
  apply prod_congr rfl
  intro i _
  rw [cutDens_ofPosVec hχ]
  simp only [rhoD_mk, ofPosVec_apply]
  rw [mul_comm]

end MultipoleBKT.ExpansionK.RouteSpatial

end
