/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.ActivityTree

/-!
# Configuration integration after the activity-tree radius allocation

See Step 3 of
the proof of Lemma A.7. Tonelli separates dipole vectors
from positions. Integrating the root and tree coordinates leaves the
written minimum-radius logarithm and the product of squared radii.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset SimpleGraph Limits Peeling SmallIntegral
open SmallIntegral.RouteJ SmallIntegral.RouteJext GeneralExpansion
open scoped Classical ENNReal

/-- Configuration integration with an arbitrary measurable root defect.
The root integral stays explicit, and no root estimate is assumed. -/
theorem lintegral_activityTree_density_le {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β M lam h : ℝ} (hlam : 0 < lam) (hM : 1 ≤ M)
    (hlh : lam ≤ h) (T : SimpleGraph W) [DecidableRel T.Adj] (hT : T.IsTree)
    (A E : Finset (Sym2 W)) (mark : Option (Sym2 W)) (root : W)
    (F : ℂ × ℂ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ c : W → ℂ × ℂ, F (c root) * activityTree M lam h T A E mark c * activityDensity χ β lam h c) ≤
      ∫⁻ u : W → ℂ, ((∫⁻ t : ℂ, F (t, t + u root)) *
        ENNReal.ofReal ((4 * Real.pi * (M ^ 2 + 5)) ^ (Fintype.card W - 1) *
          (1 + Real.log (17 * h / minRho lam u)) ^ (Fintype.card W - 1))) *
        ∏ i, cutWeight χ β lam h (u i) * ENNReal.ofReal (rho lam (u i) ^ 2) := by
  let G (c : W → ℂ × ℂ) := F (c root) * activityTree M lam h T A E mark c * activityDensity χ β lam h c
  have hG : Measurable G := ((hF.comp (measurable_pi_apply root)).mul
    (measurable_activityTree M lam h T A E mark)).mul (measurable_activityDensity hχ hlam β h)
  rw [show (fun c : W → ℂ × ℂ => F (c root) * activityTree M lam h T A E mark c *
    activityDensity χ β lam h c) = G from rfl, lintegral_eq_lintegral_pos_vec G hG]
  apply lintegral_mono
  intro u
  let dens := ∏ i, cutWeight χ β lam h (u i) * ENNReal.ofReal (rho lam (u i) ^ 2)
  have hre (x : W → ℂ) : G (ofPosVec x u) =
      (F (x root, x root + u root) * activityTree M lam h T A E mark (ofPosVec x u)) * dens := by
    dsimp only [G, ofPosVec_apply]
    rw [activityDensity_ofPosVec hχ]
  change (∫⁻ x : W → ℂ, G (ofPosVec x u)) ≤ _
  simp_rw [hre]
  have hdens : dens ≠ ⊤ := ENNReal.prod_ne_top fun i _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  rw [lintegral_mul_const' _ _ hdens]
  by_cases hu : ∀ i, ‖u i‖ ≤ h
  · exact mul_le_mul' (lintegral_activityTree_weighted_le hM hlam u
      (fun i => max_le (hu i) hlh) T hT A E mark root
      (fun t => F (t, t + u root)) (hF.comp (by fun_prop))) le_rfl
  · push Not at hu
    obtain ⟨i, hi⟩ := hu
    have hz : cutWeight χ β lam h (u i) = 0 := by
      unfold cutWeight
      rw [indicator_of_notMem (show u i ∉ Metric.closedBall (0 : ℂ) h by
        intro hx
        exact (not_le.mpr hi) (mem_closedBall_zero_iff.mp hx)), ENNReal.ofReal_zero]
    have hd : dens = 0 := prod_eq_zero (mem_univ i) (by rw [hz, zero_mul])
    simp only [hd, mul_zero]
    exact bot_le

/-- The complete logarithmic bound for the normalized spatial tree with
frozen bad points. The statement covers both the ordinary and marked trees. -/
theorem lintegral_frozen_activityTree_le_vectors {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    {p₀ N : ℕ} {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β M lam eps : ℝ} (hlam : 0 < lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) (hlh : lam ≤ eps * truncationScale p₀ β lam)
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ)
    (hV : UpperBound.badPointsOn p₀ β lam M eps V Z = V)
    (T : SimpleGraph W) [DecidableRel T.Adj] (hT : T.IsTree)
    (A E : Finset (Sym2 W)) (mark : Option (Sym2 W)) (root : W) :
    (∫⁻ c : W → ℂ × ℂ, (ENNReal.ofReal ((rhoD lam (c root) ^ 2)⁻¹) *
        rootM p₀ β lam M eps V Z ((c root).1 - (c root).2) (c root).2) *
      activityTree M lam (eps * truncationScale p₀ β lam) T A E mark c *
        activityDensity χ β lam (eps * truncationScale p₀ β lam) c) ≤
      ENNReal.ofReal ((4 * Real.pi * (M ^ 2 + 5)) ^ (Fintype.card W - 1)) *
        (ENNReal.ofReal (N / (eps * truncationScale p₀ β lam) ^ 2) *
          (∫⁻ u : W → ℂ, vectorWeight χ β lam (eps * truncationScale p₀ β lam) (Fintype.card W - 1) u) +
        ENNReal.ofReal ((128 * Real.pi + 4 * Real.pi * M ^ 2) * V.card) *
          ∫⁻ u : W → ℂ, vectorWeight χ β lam (eps * truncationScale p₀ β lam) (Fintype.card W) u) := by
  let h := eps * truncationScale p₀ β lam
  let q := Fintype.card W - 1
  let C := (4 * Real.pi * (M ^ 2 + 5)) ^ q
  let a : ℝ := N / h ^ 2
  let b : ℝ := (128 * Real.pi + 4 * Real.pi * M ^ 2) * V.card
  have hq : q + 1 = Fintype.card W := Nat.sub_add_cancel Fintype.card_pos
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  let F (d : ℂ × ℂ) := ENNReal.ofReal ((rhoD lam d ^ 2)⁻¹) * rootM p₀ β lam M eps V Z (d.1 - d.2) d.2
  have hF : Measurable F :=
    (((measurable_rhoD lam).pow_const 2).inv.ennreal_ofReal).mul
      ((measurable_rootM p₀ β lam M eps V Z).comp
        (show Measurable (fun d : ℂ × ℂ => (d.1 - d.2, d.2)) by fun_prop))
  have hM1 : 1 ≤ M := (one_le_pow₀ (by norm_num)).trans hM
  have hs := lintegral_activityTree_density_le (β := β) hχ hlam hM1 hlh T hT A E mark root F hF
  refine hs.trans ?_
  have hp (u : W → ℂ) : ((∫⁻ t : ℂ, F (t, t + u root)) *
      ENNReal.ofReal (C * (1 + Real.log (17 * h / minRho lam u)) ^ q)) *
      (∏ i, cutWeight χ β lam h (u i) * ENNReal.ofReal (rho lam (u i) ^ 2)) ≤
      ENNReal.ofReal C * (ENNReal.ofReal a * vectorWeight χ β lam h q u +
        ENNReal.ofReal b * vectorWeight χ β lam h (q + 1) u) := by
    by_cases hu : ∀ i, ‖u i‖ ≤ h
    · have heq : (∫⁻ t : ℂ, F (t, t + u root)) = ∫⁻ y : ℂ,
          ENNReal.ofReal ((max ‖-u root‖ lam ^ 2)⁻¹) * rootM p₀ β lam M eps V Z (-u root) y := by
        have hpt (t : ℂ) : F (t, t + u root) =
            ENNReal.ofReal ((max ‖-u root‖ lam ^ 2)⁻¹) * rootM p₀ β lam M eps V Z (-u root) (t + u root) := by
          dsimp only [F, rhoD]
          rw [show t - (t + u root) = -u root by ring]
        simp_rw [hpt]
        exact @lintegral_add_right_eq_self ℂ Complex.measurableSpace volume
          inferInstance inferInstance inferInstance
          (fun y : ℂ => ENNReal.ofReal ((max ‖-u root‖ lam ^ 2)⁻¹) *
            rootM p₀ β lam M eps V Z (-u root) y) (u root)
      rw [heq]
      have hr := lintegral_normalized_rootM_log_le hlam hlh hM hV
        (show ‖-u root‖ ≤ h by simpa only [norm_neg] using hu root)
        (minRho_pos hlam u) (by simpa only [norm_neg, rho] using minRho_le_rho lam u root)
      have hL : 0 ≤ 1 + Real.log (17 * h / minRho lam u) := by
        have ha0 := minRho_pos hlam u
        have hah := (minRho_le_rho lam u root).trans (max_le (hu root) hlh)
        have := Real.log_nonneg ((one_le_div ha0).2 (show minRho lam u ≤ 17 * h by linarith))
        linarith
      refine (mul_le_mul' (mul_le_mul' hr le_rfl) le_rfl).trans_eq ?_
      change ENNReal.ofReal (a + b * (1 + Real.log (17 * h / minRho lam u))) * _ * _ = _
      unfold vectorWeight
      rw [ENNReal.ofReal_add ha (mul_nonneg hb hL), ENNReal.ofReal_mul hC,
        ENNReal.ofReal_mul hb, pow_succ, ENNReal.ofReal_mul (pow_nonneg hL q)]
      ring
    · push Not at hu
      obtain ⟨i, hi⟩ := hu
      have hz : cutWeight χ β lam h (u i) = 0 := by
        unfold cutWeight
        rw [indicator_of_notMem (show u i ∉ Metric.closedBall (0 : ℂ) h by
          intro hx
          exact (not_le.mpr hi) (mem_closedBall_zero_iff.mp hx)), ENNReal.ofReal_zero]
      have hd : (∏ i, cutWeight χ β lam h (u i) * ENNReal.ofReal (rho lam (u i) ^ 2)) = 0 :=
        prod_eq_zero (mem_univ i) (by rw [hz, zero_mul])
      rw [hd, mul_zero]
      exact bot_le
  have hv (q : ℕ) : Measurable (vectorWeight (I := W) χ β lam h q) := by
    unfold vectorWeight
    apply Measurable.mul
    · exact (((measurable_const.div (measurable_minRho lam)).log.const_add 1).pow_const q).ennreal_ofReal
    · exact Finset.measurable_prod _ fun i _ =>
        ((measurable_cutWeight hχ hlam β h).comp (measurable_pi_apply i)).mul
          ((((measurable_rho lam).comp (measurable_pi_apply i)).pow_const 2).ennreal_ofReal)
  refine (lintegral_mono hp).trans_eq ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_add_left (f := fun u : W → ℂ => ENNReal.ofReal a * vectorWeight χ β lam h q u)
      ((hv q).const_mul (ENNReal.ofReal a))
      (fun u : W → ℂ => ENNReal.ofReal b * vectorWeight χ β lam h (q + 1) u),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hq]

/-- The screened model has the constant inverse-square root factor.
The same estimate applies to the marked even tree without changing its kernel. -/
theorem lintegral_screened_activityTree_le_vectors {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β M lam h : ℝ} (hlam : 0 < lam) (hM : 1 ≤ M)
    (hlh : lam ≤ h) (N : ℕ) (T : SimpleGraph W) [DecidableRel T.Adj] (hT : T.IsTree)
    (A E : Finset (Sym2 W)) (mark : Option (Sym2 W)) (root : W) :
    (∫⁻ c : W → ℂ × ℂ, ((TwoComponentCoulomb.box N).indicator 1 (c root).2 *
        ENNReal.ofReal ((h ^ 2)⁻¹)) * activityTree M lam h T A E mark c * activityDensity χ β lam h c) ≤
      ENNReal.ofReal ((4 * Real.pi * (M ^ 2 + 5)) ^ (Fintype.card W - 1) * N / h ^ 2) *
        ∫⁻ u : W → ℂ, vectorWeight χ β lam h (Fintype.card W - 1) u := by
  let F (d : ℂ × ℂ) := (TwoComponentCoulomb.box N).indicator (1 : ℂ → ℝ≥0∞) d.2 *
    ENNReal.ofReal ((h ^ 2)⁻¹)
  have hF : Measurable F := ((measurable_const.indicator
    (TwoComponentCoulomb.measurableSet_box N)).comp measurable_snd).mul measurable_const
  have hs := lintegral_activityTree_density_le (β := β) hχ hlam hM hlh T hT A E mark root F hF
  have he (u : W → ℂ) : (∫⁻ t : ℂ, F (t, t + u root)) = ENNReal.ofReal (N / h ^ 2) := by
    dsimp only [F]
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_add_right_eq_self,
      lintegral_indicator_one (TwoComponentCoulomb.measurableSet_box N), TwoComponentCoulomb.volume_box,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
  simp_rw [he] at hs
  refine hs.trans_eq ?_
  have hp (u : W → ℂ) : (ENNReal.ofReal (N / h ^ 2) *
      ENNReal.ofReal ((4 * Real.pi * (M ^ 2 + 5)) ^ (Fintype.card W - 1) *
        (1 + Real.log (17 * h / minRho lam u)) ^ (Fintype.card W - 1))) *
      (∏ i, cutWeight χ β lam h (u i) * ENNReal.ofReal (rho lam (u i) ^ 2)) =
      ENNReal.ofReal ((4 * Real.pi * (M ^ 2 + 5)) ^ (Fintype.card W - 1) * N / h ^ 2) *
        vectorWeight χ β lam h (Fintype.card W - 1) u := by
    unfold vectorWeight
    let K := (4 * Real.pi * (M ^ 2 + 5)) ^ (Fintype.card W - 1)
    have hK : 0 ≤ K := by dsimp only [K]; positivity
    rw [ENNReal.ofReal_mul hK]
    have he : ENNReal.ofReal (N / h ^ 2) * ENNReal.ofReal K = ENNReal.ofReal (K * N / h ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    calc
      _ = (ENNReal.ofReal (N / h ^ 2) * ENNReal.ofReal K) *
          (ENNReal.ofReal ((1 + Real.log (17 * h / minRho lam u)) ^ (Fintype.card W - 1)) *
            ∏ i, cutWeight χ β lam h (u i) * ENNReal.ofReal (rho lam (u i) ^ 2)) := by ring
      _ = _ := by rw [he]

  simp_rw [hp]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end MultipoleBKT.ExpansionK.RouteSpatial

end
