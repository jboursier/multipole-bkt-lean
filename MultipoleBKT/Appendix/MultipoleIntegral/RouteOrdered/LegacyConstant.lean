/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.Reduction

/-!
# Numerical compatibility with the explicit upper constant

See (A.13) and (A.14). The paper leaves the coefficient unspecified. The
public interfaces prescribe a particular coefficient. After the
ordered reduction, this file compares its scalar coefficient with that
prescribed value. This extra numerical comparison is not used to replace
the endpoint decomposition or the ordered configuration integral.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegral

open MeasureTheory Finset Set
open scoped ENNReal Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Internal numerical comparison on a maximum sector at unit core
radius. The geometric-mean inequality is used only here to
retain the prescribed value of `upperConst`. -/
theorem internal_orderedSector_le_product (β h : ℝ) (root : ι) (x : ι → ℂ) :
    orderedSector β 1 h root x ≤
      ∏ i, ENNReal.ofReal (max ‖x i‖ 1 ^ (2 - 2 / (Fintype.card ι : ℝ) - β)) := by
  let a : ℝ := 2 - 2 / (Fintype.card ι : ℝ)
  by_cases hmax : ∀ i, ‖x i‖ ≤ ‖x root‖
  · calc
      _ ≤ ENNReal.ofReal (max ‖x root‖ 1 ^ (-β)) *
          ∏ i ∈ univ.erase root, ENNReal.ofReal (max ‖x i‖ 1 ^ (2 - β)) := by
        apply mul_le_mul' (indicator_le_self _ _ _)
        exact prod_le_prod fun i _ => indicator_le_self _ _ _
      _ = ENNReal.ofReal (∏ i ∈ univ.erase root, max ‖x i‖ 1 ^ 2) *
          ∏ i, ENNReal.ofReal (max ‖x i‖ 1 ^ (-β)) :=
        (internal_root_product_eq (by norm_num : (0 : ℝ) < 1) β x root).symm
      _ ≤ ENNReal.ofReal (∏ i, max ‖x i‖ 1 ^ a) *
          ∏ i, ENNReal.ofReal (max ‖x i‖ 1 ^ (-β)) := by
        apply mul_le_mul' _ le_rfl
        exact ENNReal.ofReal_le_ofReal (prod_erase_sq_le_prod_rpow
          (fun i => max ‖x i‖ 1) (fun i => by positivity) root
          (fun i => max_le_max (hmax i) le_rfl))
      _ = _ := by
        rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity), ← prod_mul_distrib]
        apply prod_congr rfl
        intro i _
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ max ‖x i‖ 1 ^ a),
          ← Real.rpow_add (by positivity : 0 < max ‖x i‖ 1)]
        congr 2
  · push Not at hmax
    obtain ⟨i, hi⟩ := hmax
    have hne : i ≠ root := by intro he; subst i; exact lt_irrefl _ hi
    have hzero : (∏ c ∈ univ.erase root, (Metric.closedBall (0 : ℂ) ‖x root‖).indicator
        (fun z => ENNReal.ofReal (max ‖z‖ 1 ^ (2 - β))) (x c)) = 0 := by
      apply prod_eq_zero (mem_erase.mpr ⟨hne, mem_univ i⟩)
      apply indicator_of_notMem
      simpa only [Metric.mem_closedBall, dist_zero_right] using not_le.mpr hi
    unfold orderedSector
    rw [hzero, mul_zero]
    exact zero_le

/-- Internal finite-cutoff comparison for the prescribed numerical
constant. The actual ordered polar integral is retained on the left. -/
theorem internal_ordered_coefficient_finite (root : ι) {β : ℝ}
    (hk : 2 - 2 / (Fintype.card ι : ℝ) - β < -2) (h : ℝ) :
    ENNReal.ofReal (2 * Real.pi) ^ Fintype.card ι *
      orderedRadial β 1 (Ioc 0 h) (Fintype.card ι - 1) ≤
        ENNReal.ofReal (∫ z : ℂ, max ‖z‖ 1 ^
          (2 - 2 / (Fintype.card ι : ℝ) - β)) ^ Fintype.card ι := by
  rw [← lintegral_orderedSector (by norm_num : (0 : ℝ) < 1) β h root]
  refine (lintegral_mono (internal_orderedSector_le_product β h root)).trans (le_of_eq ?_)
  have hm : Measurable fun z : ℂ => ENNReal.ofReal
      (max ‖z‖ 1 ^ (2 - 2 / (Fintype.card ι : ℝ) - β)) :=
    ENNReal.measurable_ofReal.comp (((continuous_norm.max continuous_const).rpow_const
      (fun z => Or.inl (by positivity : (max ‖z‖ 1 : ℝ) ≠ 0))).measurable)
  rw [lintegral_pi_prod_eq _ (fun _ => hm)]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_max_norm_rpow (by norm_num : (0 : ℝ) < 1) hk)
    (Filter.Eventually.of_forall fun z => by positivity), prod_const, card_univ]

/-- Internal infinite-cutoff comparison for the prescribed numerical
constant, obtained by monotone exhaustion of the ordered integral. -/
theorem internal_ordered_coefficient_infinite (root : ι) {β : ℝ}
    (hk : 2 - 2 / (Fintype.card ι : ℝ) - β < -2) :
    ENNReal.ofReal (2 * Real.pi) ^ Fintype.card ι *
      orderedRadial β 1 (Ioi 0) (Fintype.card ι - 1) ≤
        ENNReal.ofReal (∫ z : ℂ, max ‖z‖ 1 ^
          (2 - 2 / (Fintype.card ι : ℝ) - β)) ^ Fintype.card ι := by
  let A : ℝ≥0∞ := ENNReal.ofReal (2 * Real.pi) ^ Fintype.card ι
  have hA0 : A ≠ 0 := by dsimp only [A]; positivity
  have hAfin : A ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  rw [mul_comm]
  apply (ENNReal.le_div_iff_mul_le (b := A) (Or.inl hA0) (Or.inl hAfin)).mp
  apply internal_orderedRadial_infinite_of_finite (by norm_num : (0 : ℝ) < 1)
  intro h _
  apply (ENNReal.le_div_iff_mul_le (b := A) (Or.inl hA0) (Or.inl hAfin)).mpr
  simpa only [A, mul_comm] using internal_ordered_coefficient_finite root hk h

end MultipoleBKT.MultipoleIntegral

end
