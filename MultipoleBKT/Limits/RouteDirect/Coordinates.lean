/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteDirect.Anchor
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.TreeCoordinates
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.ProductCoordinates

/-!
# The literal relative coordinates of the limiting integrands

See (4.48), (4.50),
and Lemma 4.26. The carrier has
`2|I|-1` complex coordinates. The common translation is fixed at zero.
-/

@[expose] public section

namespace MultipoleBKT.Limits.RouteDirect

open MeasureTheory Finset Set
open SmallIntegral.RouteJ
open scoped ENNReal Classical
open TwoComponentCoulomb (box)

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The first endpoints other than the root, and all second endpoints. -/
abbrev RelativeCoordinates (root : I) := ({i : I // i ≠ root} → ℂ) × (I → ℂ)

/-- Reinsert the fixed first endpoint at the origin. -/
def originPositions (root : I) (x : {i : I // i ≠ root} → ℂ) (i : I) : ℂ :=
  if hi : i = root then 0 else x ⟨i, hi⟩

/-- The configuration with the root at zero and the supplied relative endpoints. -/
def relativeLift (root : I) (p : RelativeCoordinates root) : I → ℂ × ℂ :=
  fun i => (originPositions root p.1 i, p.2 i)

/-- The relative endpoint variables displayed in the paper. -/
def relativeEndpoints (root : I) (c : I → ℂ × ℂ) : RelativeCoordinates root :=
  (fun i => (c i).1 - (c root).1, fun i => (c i).2 - (c root).1)

omit [Fintype I] in
/-- The relative endpoints describe the configuration translated to its root. -/
theorem relativeLift_relativeEndpoints (root : I) (c : I → ℂ × ℂ) :
    relativeLift root (relativeEndpoints root c) = translate (-(c root).1) c := by
  funext i
  apply Prod.ext
  · change originPositions root (fun j => (c j).1 - (c root).1) i = (c i).1 + -(c root).1
    unfold originPositions
    split_ifs with hi
    · subst i
      ring
    · ring
  · change (c i).2 - (c root).1 = (c i).2 + -(c root).1
    ring

omit [Fintype I] in
/-- The fixed-origin coordinate map is measurable. -/
theorem measurable_relativeLift (root : I) : Measurable (relativeLift root) := by
  apply measurable_pi_iff.mpr
  intro i
  unfold relativeLift originPositions
  split_ifs <;> fun_prop

/-- Fixing the origin has Jacobian one. This identifies the rooted integral
with the literal `(2|I|-1)`-coordinate integral used in the paper. -/
theorem lintegral_anchor_eq_relative (root : I) {F : (I → ℂ × ℂ) → ℝ≥0∞}
    (hF : Measurable F) (hinv : TranslationInvariant F) :
    (∫⁻ c, anchor root c * F c) = ∫⁻ p : RelativeCoordinates root, F (relativeLift root p) := by
  have hm0 : Measurable (fun c => anchor root c * F c) := (measurable_anchor root).mul hF
  rw [lintegral_eq_lintegral_pos_vec _ hm0]
  have hzero (u x : I → ℂ) :
      F (ofPosVec x u) = F (ofPosVec (fun i => x i - x root) u) := by
    have h := hinv (-(x root)) (ofPosVec x u)
    have heq : translate (-(x root)) (ofPosVec x u) = ofPosVec (fun i => x i - x root) u := by
      funext i
      ext <;> simp [translate, ofPosVec_apply] <;> ring
    rw [heq] at h
    exact h.symm
  have hpos (u : I → ℂ) :
      (∫⁻ x : I → ℂ, anchor root (ofPosVec x u) * F (ofPosVec x u)) =
      ∫⁻ z : {i : I // i ≠ root} → ℂ, F (ofPosVec (originPositions root z) u) := by
    let H : (I → ℂ) → ℝ≥0∞ := fun x =>
      (box 1).indicator 1 (x root) * F (ofPosVec (originPositions root (fun i => x i)) u)
    have hH : Measurable H := by
      apply Measurable.mul ((measurable_one.indicator (TwoComponentCoulomb.measurableSet_box 1)).comp
        (measurable_pi_apply root))
      apply hF.comp
      refine measurable_pi_iff.mpr fun i => ?_
      unfold ofPosVec originPositions
      split_ifs <;> fun_prop
    have hcoords := lintegral_treeCoordinates root (fun _ => root)
      (fun i : I => if i = root then 0 else 1) (by intro i hi; simp [hi])
      (fun _ => 0) H hH
    have heq (x : I → ℂ) : H (treeCoordinates root (fun _ => root) (fun _ => 0) x) =
        anchor root (ofPosVec x u) * F (ofPosVec x u) := by
      dsimp only [H]
      have ho : originPositions root
          (fun i => treeCoordinates root (fun _ => root) (fun _ => 0) x i) =
          fun i => x i - x root := by
        funext i
        by_cases hi : i = root <;> simp [originPositions, treeCoordinates, hi]
      rw [ho, ← hzero u x]
      simp only [treeCoordinates, ite_true, anchor, ofPosVec_apply]
    simp_rw [heq] at hcoords
    rw [hcoords]
    have hm : Measurable fun z : {i : I // i ≠ root} → ℂ =>
        F (ofPosVec (originPositions root z) u) := by
      apply hF.comp
      refine measurable_pi_iff.mpr fun i => ?_
      unfold ofPosVec originPositions
      split_ifs <;> fun_prop
    rw [lintegral_root_coordinates root _
      (measurable_one.indicator (TwoComponentCoulomb.measurableSet_box 1)) _ hm,
      lintegral_indicator_one (TwoComponentCoulomb.measurableSet_box 1),
      TwoComponentCoulomb.volume_box]
    simp only [Nat.cast_one, one_mul]
  change (∫⁻ u : I → ℂ, ∫⁻ x : I → ℂ,
    anchor root (ofPosVec x u) * F (ofPosVec x u)) = _
  simp_rw [hpos]
  have hm : Measurable (Function.uncurry fun (u : I → ℂ) (x : {i : I // i ≠ root} → ℂ) =>
      F (ofPosVec (originPositions root x) u)) := by
    apply hF.comp
    refine measurable_pi_iff.mpr fun i => ?_
    unfold ofPosVec originPositions
    split_ifs <;> fun_prop
  have hmrel : Measurable (fun p : RelativeCoordinates root => F (relativeLift root p)) :=
    hF.comp (measurable_relativeLift root)
  rw [lintegral_lintegral_swap hm.aemeasurable, Measure.volume_eq_prod,
    lintegral_prod _ hmrel.aemeasurable]
  apply lintegral_congr
  intro x
  have hp := (measurePreserving_add_left (volume : Measure (I → ℂ))
    (originPositions root x)).lintegral_comp
      (hF.comp (show Measurable (fun y : I → ℂ => relativeLift root (x, y)) by
        apply measurable_pi_iff.mpr
        intro i
        change Measurable (fun y : I → ℂ => (originPositions root x i, y i))
        exact measurable_const.prodMk (measurable_pi_apply i)))
  exact hp

/-- Integrability on the literal relative-coordinate carrier. -/
theorem integrable_relative (root : I) {F : (I → ℂ × ℂ) → ℝ}
    (hF : Measurable F) (hinv : TranslationInvariant F)
    (hint : Integrable fun c => anchorR root c * F c) :
    Integrable fun p : RelativeCoordinates root => F (relativeLift root p) := by
  refine ⟨(hF.comp (measurable_relativeLift root)).aestronglyMeasurable, ?_⟩
  have hf := hint.2
  unfold HasFiniteIntegral at hf ⊢
  simp_rw [enorm_anchorR_mul] at hf
  rw [lintegral_anchor_eq_relative root hF.enorm (fun a c => by rw [hinv a c])] at hf
  exact hf

/-- Equality of the real integrals in rooted and fixed-origin coordinates. -/
theorem integral_anchor_eq_relative (root : I) {F : (I → ℂ × ℂ) → ℝ}
    (hF : Measurable F) (hinv : TranslationInvariant F)
    (hint : Integrable fun c => anchorR root c * F c) :
    (∫ c, anchorR root c * F c) = ∫ p : RelativeCoordinates root, F (relativeLift root p) := by
  have hrel := integrable_relative root hF hinv hint
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hrel]
  congr 2
  · simp_rw [ENNReal.ofReal_mul (anchorR_nonneg root _), ofReal_anchorR]
    exact lintegral_anchor_eq_relative root hF.ennreal_ofReal (fun a c => by rw [hinv a c])
  · have heq (c : I → ℂ × ℂ) : -(anchorR root c * F c) = anchorR root c * (-F c) := by ring
    simp_rw [heq, ENNReal.ofReal_mul (anchorR_nonneg root _), ofReal_anchorR]
    exact lintegral_anchor_eq_relative root hF.neg.ennreal_ofReal (fun a c => by rw [hinv a c])

end MultipoleBKT.Limits.RouteDirect

end
