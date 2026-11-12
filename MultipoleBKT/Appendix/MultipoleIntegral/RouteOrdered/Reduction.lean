/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.Polar

/-!
# The single-tree ordered radial upper bound

See (A.11), (A.12) and (A.13). Split by a largest radius, use the ordering-tree
lemma, retain the root power, and integrate every other radius below it.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegral

open MeasureTheory Set Finset
open scoped ENNReal Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem measurable_orderedSector {lam : ℝ} (hlam : 0 < lam)
    (β h : ℝ) (root : ι) : Measurable (orderedSector β lam h root) := by
  have hP (a : ℝ) : Measurable fun z : ℂ => ENNReal.ofReal (max ‖z‖ lam ^ a) :=
    ENNReal.measurable_ofReal.comp ((continuous_norm.max continuous_const).rpow_const
      (fun z => Or.inl (lt_max_of_lt_right hlam).ne')).measurable
  unfold orderedSector
  refine (((hP _).indicator measurableSet_closedBall).comp (measurable_pi_apply root)).mul ?_
  apply Finset.measurable_prod
  intro c _
  have heq : (fun x : ι → ℂ => (Metric.closedBall (0 : ℂ) ‖x root‖).indicator
      (fun z => ENNReal.ofReal (max ‖z‖ lam ^ (2 - β))) (x c)) =
      fun x => if ‖x c‖ ≤ ‖x root‖ then ENNReal.ofReal (max ‖x c‖ lam ^ (2 - β)) else 0 := by
    funext x
    simp [Set.indicator, Metric.mem_closedBall, dist_zero_right]
  rw [heq]
  exact Measurable.ite (measurableSet_le (measurable_pi_apply c).norm
    (measurable_pi_apply root).norm) ((hP _).comp (measurable_pi_apply c)) measurable_const

/-- Internal regrouping of the root and non-root powers. -/
theorem internal_root_product_eq {lam : ℝ} (hlam : 0 < lam) (β : ℝ) (x : ι → ℂ) (root : ι) :
    ENNReal.ofReal (∏ i ∈ univ.erase root, max ‖x i‖ lam ^ 2) *
        ∏ i, ENNReal.ofReal (max ‖x i‖ lam ^ (-β)) =
      ENNReal.ofReal (max ‖x root‖ lam ^ (-β)) *
        ∏ i ∈ univ.erase root, ENNReal.ofReal (max ‖x i‖ lam ^ (2 - β)) := by
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => sq_nonneg _),
    ← mul_prod_erase univ (fun i => ENNReal.ofReal (max ‖x i‖ lam ^ (-β))) (mem_univ root)]
  rw [mul_left_comm]
  congr 1
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  rw [← ENNReal.ofReal_mul (sq_nonneg _), ← Real.rpow_two,
    ← Real.rpow_add (lt_max_of_lt_right hlam)]
  congr 2

/-- The regularized tree radial bound in (A.13). This retains the full
nested integral, with the cutoff and all radii unscaled. -/
theorem lintegral_tree_radial_le [Nonempty ι] {T : SimpleGraph ι} (hT : T.IsTree)
    {lam : ℝ} (hlam : 0 < lam) (β h : ℝ) :
    ∫⁻ x : ι → ℂ, {x : ι → ℂ | ∀ i, ‖x i‖ ≤ h}.indicator
      (fun x => ENNReal.ofReal
        (∏ e ∈ T.edgeFinset, edgeMin (fun t => max t lam ^ 2) (fun i => ‖x i‖) e) *
          ∏ i, ENNReal.ofReal (max ‖x i‖ lam ^ (-β))) x ≤
      (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi) ^ Fintype.card ι *
        orderedRadial β lam (Ioc 0 h) (Fintype.card ι - 1) := by
  have hpt : ∀ x : ι → ℂ, {x : ι → ℂ | ∀ i, ‖x i‖ ≤ h}.indicator
      (fun x => ENNReal.ofReal
        (∏ e ∈ T.edgeFinset, edgeMin (fun t => max t lam ^ 2) (fun i => ‖x i‖) e) *
          ∏ i, ENNReal.ofReal (max ‖x i‖ lam ^ (-β))) x ≤
      ∑ root, orderedSector β lam h root x := by
    intro x
    by_cases hx : ∀ i, ‖x i‖ ≤ h
    · rw [indicator_of_mem (show x ∈ {x : ι → ℂ | ∀ i, ‖x i‖ ≤ h} from hx)]
      refine (tree_radius_weight_le_sum_ordered hT hlam.le (fun i => ‖x i‖)
        (fun i => ENNReal.ofReal (max ‖x i‖ lam ^ (-β)))).trans ?_
      apply sum_le_sum
      intro root _
      by_cases hr : ∀ i, ‖x i‖ ≤ ‖x root‖
      · rw [ite_eq_left hr, one_mul, internal_root_product_eq hlam]
        unfold orderedSector
        rw [indicator_of_mem (show x root ∈ Metric.closedBall (0 : ℂ) h by
          simpa [Metric.mem_closedBall, dist_zero_right] using hx root)]
        apply le_of_eq
        congr 1
        apply prod_congr rfl
        intro i _
        rw [indicator_of_mem (show x i ∈ Metric.closedBall (0 : ℂ) ‖x root‖ by
          simpa [Metric.mem_closedBall, dist_zero_right] using hr i)]
      · rw [ite_eq_right hr, zero_mul]
        exact zero_le
    · rw [indicator_of_notMem (show x ∉ {x : ι → ℂ | ∀ i, ‖x i‖ ≤ h} from hx)]
      exact zero_le
  calc
    _ ≤ ∫⁻ x : ι → ℂ, ∑ root, orderedSector β lam h root x := lintegral_mono hpt
    _ = ∑ root : ι, ∫⁻ x : ι → ℂ, orderedSector β lam h root x :=
      lintegral_finsetSum _ (fun root _ => measurable_orderedSector hlam β h root)
    _ = _ := by
      simp_rw [lintegral_orderedSector hlam]
      rw [sum_const, card_univ, nsmul_eq_mul]
      ring

/-- The single-tree bound (A.13) with the actual smoothed dipole weights.
The only kernel estimate is the paper's regularized logarithmic
upper bound. All inner radii remain below the largest one. -/
theorem lintegral_tree_smoothed_le [Nonempty ι] {T : SimpleGraph ι} (hT : T.IsTree)
    {χ : ℂ → ℝ} (hχ : IsMollifier χ) {lam β : ℝ} (hlam : 0 < lam) (hβ : 0 ≤ β) (h : ℝ) :
    ∫⁻ x : ι → ℂ, {x : ι → ℂ | ∀ i, ‖x i‖ ≤ h}.indicator
      (fun x => ENNReal.ofReal
        (∏ e ∈ T.edgeFinset, edgeMin (fun t => max t lam ^ 2) (fun i => ‖x i‖) e) *
          ∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam (x i)))) x ≤
      ENNReal.ofReal (Real.exp (β * kernelConst χ)) ^ Fintype.card ι *
        ((Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi) ^ Fintype.card ι *
          orderedRadial β lam (Ioc 0 h) (Fintype.card ι - 1)) := by
  let C := ENNReal.ofReal (Real.exp (β * kernelConst χ)) ^ Fintype.card ι
  have hpt : ∀ x : ι → ℂ, {x : ι → ℂ | ∀ i, ‖x i‖ ≤ h}.indicator
      (fun x => ENNReal.ofReal
        (∏ e ∈ T.edgeFinset, edgeMin (fun t => max t lam ^ 2) (fun i => ‖x i‖) e) *
          ∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam (x i)))) x ≤
      C * {x : ι → ℂ | ∀ i, ‖x i‖ ≤ h}.indicator
        (fun x => ENNReal.ofReal
          (∏ e ∈ T.edgeFinset, edgeMin (fun t => max t lam ^ 2) (fun i => ‖x i‖) e) *
            ∏ i, ENNReal.ofReal (max ‖x i‖ lam ^ (-β))) x := by
    intro x
    by_cases hx : x ∈ {x : ι → ℂ | ∀ i, ‖x i‖ ≤ h}
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      have hp : (∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam (x i)))) ≤
          C * ∏ i, ENNReal.ofReal (max ‖x i‖ lam ^ (-β)) := by
        calc
          _ ≤ ∏ i, ENNReal.ofReal (Real.exp (β * kernelConst χ)) *
              ENNReal.ofReal (max ‖x i‖ lam ^ (-β)) := by
            apply Finset.prod_le_prod
            intro i _
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
            exact ENNReal.ofReal_le_ofReal (exp_smearedKernel_le hχ hβ hlam (x i))
          _ = _ := by rw [prod_mul_distrib, prod_const, card_univ]
      calc
        _ ≤ _ := mul_le_mul' le_rfl hp
        _ = _ := by ring
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]
  calc
    _ ≤ ∫⁻ x : ι → ℂ, C * {x : ι → ℂ | ∀ i, ‖x i‖ ≤ h}.indicator
        (fun x => ENNReal.ofReal
          (∏ e ∈ T.edgeFinset, edgeMin (fun t => max t lam ^ 2) (fun i => ‖x i‖) e) *
            ∏ i, ENNReal.ofReal (max ‖x i‖ lam ^ (-β))) x := lintegral_mono hpt
    _ = C * ∫⁻ x : ι → ℂ, {x : ι → ℂ | ∀ i, ‖x i‖ ≤ h}.indicator
        (fun x => ENNReal.ofReal
          (∏ e ∈ T.edgeFinset, edgeMin (fun t => max t lam ^ 2) (fun i => ‖x i‖) e) *
            ∏ i, ENNReal.ofReal (max ‖x i‖ lam ^ (-β))) x :=
      lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    _ ≤ _ := mul_le_mul' le_rfl (lintegral_tree_radial_le hT hlam β h)

end MultipoleBKT.MultipoleIntegral

end
