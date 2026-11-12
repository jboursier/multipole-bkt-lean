/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.API

/-!
# The omitted quadratic minimum

See Lemma A.7. The cutoff square is factored
once from the entire odd family, including the empty family.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteOmitted

open MeasureTheory Set Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ SmallIntegral.RouteJext UpperBound.BoundedUpper RouteCases RouteSpatial
open scoped Classical ENNReal

/-- Factoring the quadratic minimum changes the single tail scale to `H`.
This identity also covers zero distances and the empty edge family. -/
theorem quadratic_globalTail {I : Type*} [DecidableEq I] {R H : ℝ}
    (hR : 0 < R) (hH : 0 < H) (hRH : R ≤ H) (d : I → ℝ) (A : Finset I) :
    min (R ^ 2 / H ^ 2) (globalTail R d A) =
      (R ^ 2 / H ^ 2) * globalTail H d A := by
  let q := R ^ 2 / H ^ 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := (div_le_one (pow_pos hH 2)).2 (pow_le_pow_left₀ hR.le hRH 2)
  have he (i : I) : min q (min 1 (R ^ 2 / d i ^ 2)) = q * min 1 (H ^ 2 / d i ^ 2) := by
    rw [← min_assoc,min_eq_left hq1,mul_min_of_nonneg _ _ hq.le,mul_one]
    congr 1
    dsimp [q]
    field_simp
  change min q (globalTail R d A) = q * globalTail H d A
  induction A using Finset.induction_on with
  | empty => simp only [globalTail,fold_empty,mul_one,min_eq_left hq1]
  | @insert i A hi ih =>
    simp only [globalTail,fold_insert hi]
    change min q (min (min 1 (R ^ 2 / d i ^ 2)) (globalTail R d A)) =
      q * min (min 1 (H ^ 2 / d i ^ 2)) (globalTail H d A)
    calc
      _ = min (min q (min 1 (R ^ 2 / d i ^ 2))) (min q (globalTail R d A)) := by
        apply le_antisymm
        · exact le_min (min_le_min_left _ (min_le_left _ _)) (min_le_min_left _ (min_le_right _ _))
        · exact le_min ((min_le_left _ _).trans (min_le_left _ _))
            (le_min ((min_le_left _ _).trans (min_le_right _ _)) ((min_le_right _ _).trans (min_le_right _ _)))
      _ = _ := by rw [he,ih,← mul_min_of_nonneg _ _ hq.le]

/-- The omitted density is bounded by the same cut density used in spatial integration. -/
theorem omittedDensity_le_cutDens {W : Type*} [Fintype W]
    (χ : ℂ → ℝ) (β lam h : ℝ) (Df : Finset (Sym2 W)) (c : W → ℂ × ℂ) :
    omittedDensity χ β lam h Df c ≤ ∏ i, cutDens χ β lam h (c i) := by
  have he : mixedDensity χ β lam h ∅ c = ∏ i, cutDens χ β lam h (c i) := by
    have hprod : (∏ i, cutDens χ β lam h (c i)) =
        (∏ i, pairDensity χ β lam (c i)) * cutInd h c := by
      unfold cutDens cutInd
      rw [← prod_mul_distrib]
      apply prod_congr rfl
      intro i _
      split_ifs with hi
      · rw [indicator_of_mem (show ‖(c i).1-(c i).2‖ ∈ Iic h from hi)]; rfl
      · rw [indicator_of_notMem (show ‖(c i).1-(c i).2‖ ∉ Iic h from hi)]
    simpa only [mixedDensity,shortInd,Finset.prod_empty,mul_one] using hprod.symm
  rw [← he]
  unfold omittedDensity mixedDensity
  simp only [shortInd,Finset.prod_empty,mul_one]
  exact mul_le_of_le_one_right
    (mul_nonneg (prod_nonneg fun _ _ => (pairDensity_pos _ _ _ _).le) (cutInd_nonneg _ _))
    (sub_le_self _ (shortInd_nonneg _ _ _))

/-- Common support and omitted density are multiplied after spatial allocation. -/
theorem internal_common_normalization {W B : Type*} [Fintype W] [DecidableEq W]
    [Fintype B] [DecidableEq B] (χ : ℂ → ℝ) (β M lam h : ℝ)
    (blk : W → B) (Dn Dz Df : Finset (Sym2 W)) (c : W → ℂ × ℂ)
    {z : ℝ} {T : ℝ≥0∞}
    (hn : ENNReal.ofReal z ≤ ENNReal.ofReal (∏ i, rhoD lam (c i) ^ 2) * T) :
    ENNReal.ofReal (clusterSupport M lam blk Dn Dz c * omittedDensity χ β lam h Df c * z) ≤
      T * activityDensity χ β lam h c := by
  have hS := clusterSupport_nonneg M lam blk Dn Dz c
  have hD := omittedDensity_nonneg χ β lam h Df c
  have hs : ENNReal.ofReal (clusterSupport M lam blk Dn Dz c) ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (clusterSupport_le_one M lam blk Dn Dz c)
  rw [mul_assoc,ENNReal.ofReal_mul hS,ENNReal.ofReal_mul hD]
  refine (mul_le_mul' hs (mul_le_mul'
    (ENNReal.ofReal_le_ofReal (omittedDensity_le_cutDens χ β lam h Df c)) hn)).trans_eq ?_
  rw [one_mul]
  calc
    _ = T * (ENNReal.ofReal (∏ i, rhoD lam (c i) ^ 2) *
        ENNReal.ofReal (∏ i, cutDens χ β lam h (c i))) := by ring
    _ = _ := by rw [radial_mul_density]

end MultipoleBKT.ExpansionK.RouteOmitted

end
