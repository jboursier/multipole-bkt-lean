/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeTwoIntegral.CutWeight
public import MultipoleBKT.UpperBound.BadPointTypes.TypeTwoTwo
public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.API

/-!
# Endpoint cells for type-two blocks

The paper: (5.136) and
(5.137). The tree change of variables supplies the four endpoint cells and
Jacobian-one coordinates. The tree sum keeps the exact edge minima.
-/

@[expose] public section

namespace MultipoleBKT.BadPointTypes

open MeasureTheory Finset MultipoleIntegral
open scoped ENNReal Classical
open TwoComponentCoulomb (box)

variable {χ : ℂ → ℝ} {β lam M : ℝ}
variable {ι : Type*} [Fintype ι]

/-- The cutoff configuration weight is the connected weight with a radial factor. -/
theorem blockWeight_cut_eq (h : ℝ) (N : ℕ) (c : ι → ℂ × ℂ) :
    blockWeight M lam (cutDipoleWeight χ β lam h N) c =
      radialCut h (fun i => (c i).1 - (c i).2) * connectedWeight χ N β lam M c := by
  by_cases hb : ∀ i, c i ∈ box N ×ˢ box N
  · have hbox : c ∈ Set.univ.pi (fun _ : ι => box N ×ˢ box N) := Set.mem_univ_pi.mpr hb
    unfold blockWeight connectedWeight radialCut
    rw [Set.indicator_of_mem hbox]
    have heq : ∀ i, cutDipoleWeight χ β lam h N (c i) = cutFactor χ β lam h ((c i).1 - (c i).2) := by
      intro i
      exact Set.indicator_of_mem (hb i) _
    simp_rw [heq]
    by_cases hr : ∀ i, ‖(c i).1 - (c i).2‖ ≤ h
    · have he : ∀ i, cutFactor χ β lam h ((c i).1 - (c i).2) =
          ENNReal.ofReal (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2))) := by
        intro i
        apply Set.indicator_of_mem
        simpa only [Metric.mem_closedBall, dist_zero_right] using hr i
      simp_rw [he]
      rw [ite_eq_left hr, one_mul]
      split_ifs <;> rfl
    · obtain ⟨i, hi⟩ := not_forall.mp hr
      have hz : cutFactor χ β lam h ((c i).1 - (c i).2) = 0 := by
        apply Set.indicator_of_notMem
        simpa only [Metric.mem_closedBall, dist_zero_right] using hi
      rw [ite_eq_right hr, zero_mul, prod_eq_zero (mem_univ i) hz, mul_zero]
  · obtain ⟨i, hi⟩ := not_forall.mp hb
    have hbox : c ∉ Set.univ.pi (fun _ : ι => box N ×ˢ box N) :=
      fun hc => hi (Set.mem_univ_pi.mp hc i)
    unfold blockWeight connectedWeight
    rw [Set.indicator_of_notMem hbox, mul_zero,
      prod_eq_zero (mem_univ i) (Set.indicator_of_notMem hi _), mul_zero]

/-- The actual-tree radial reduction after endpoint-cell integration.
This is the single-block form of the spatial estimate before (5.138). -/
theorem lintegral_blockWeight_cut_tree_le [Nonempty ι]
    (hχ : IsMollifier χ) (hlam : 0 < lam) (hM : 0 ≤ M) (h : ℝ) (N : ℕ) :
    ∫⁻ c : ι → ℂ × ℂ, blockWeight M lam (cutDipoleWeight χ β lam h N) c ≤
      (N : ℝ≥0∞) * ENNReal.ofReal (4 * Real.pi * M ^ 2) ^ (Fintype.card ι - 1) *
        ∑ T ∈ (univ : Finset (SimpleGraph ι)).filter (fun T => T.IsTree),
          ∫⁻ r : ι → ℂ, radialCut h r * treeDipoleWeight T χ β lam r := by
  calc
    _ = ∫⁻ c : ι → ℂ × ℂ, radialCut h (fun i => (c i).1 - (c i).2) *
        connectedWeight χ N β lam M c := lintegral_congr (blockWeight_cut_eq h N)
    _ ≤ _ := lintegral_connectedWeight_radial_reduction hχ hlam hM N _ (measurable_radialCut h)

/-- Cayley's count in the fixed-root spatial fiber. The four endpoint choices
are already included in the coefficient `4πM²`. -/
theorem lintegral_positions_cayley_le [Nonempty ι] (hM : 0 ≤ M) (hlam : 0 ≤ lam)
    (N : ℕ) (r : ι → ℂ) (root : ι) :
    ∫⁻ y : ι → ℂ, (box N).indicator (1 : ℂ → ℝ≥0∞) (y root) *
      connectedIndicator M lam y r ≤
      ((Fintype.card ι ^ (Fintype.card ι - 2) : ℕ) : ℝ≥0∞) * (N : ℝ≥0∞) *
        ∏ c ∈ univ.erase root, ENNReal.ofReal (4 * Real.pi * (M * max ‖r c‖ lam) ^ 2) := by
  have hred := lintegral_connected_positions_tree_le hM hlam r root
    (TwoComponentCoulomb.measurableSet_box N)
  rw [TwoComponentCoulomb.volume_box] at hred
  have hsum : (∑ T ∈ (univ : Finset (SimpleGraph ι)).filter (fun T => T.IsTree),
      ENNReal.ofReal (∏ e ∈ T.edgeFinset,
        edgeMin (fun t => max t lam ^ 2) (fun i => ‖r i‖) e)) ≤
      ((Fintype.card ι ^ (Fintype.card ι - 2) : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (∏ c ∈ univ.erase root, max ‖r c‖ lam ^ 2) := by
    calc
      _ ≤ ∑ _T ∈ (univ : Finset (SimpleGraph ι)).filter (fun T => T.IsTree),
          ENNReal.ofReal (∏ c ∈ univ.erase root, max ‖r c‖ lam ^ 2) := by
        apply sum_le_sum
        intro T hT
        apply ENNReal.ofReal_le_ofReal
        apply prod_edgeMin_le_prod_erase (mem_filter.mp hT).2 _ (fun _ => sq_nonneg _) _ root
        intro a b hab
        exact pow_le_pow_left₀ (le_max_of_le_right hlam) (max_le_max hab le_rfl) 2
      _ = _ := by rw [sum_const, nsmul_eq_mul, card_trees_eq_pow]
  have heq (y : ι → ℂ) : connectedIndicator M lam y r =
      (if (SimpleGraph.fromRel fun i j =>
        MultipoleLinked M lam (y i + r i, y i) (y j + r j, y j)).Connected
        then (1 : ℝ≥0∞) else 0) := by
    unfold connectedIndicator
    split_ifs <;> rfl
  simp_rw [heq]
  refine hred.trans ((mul_le_mul' le_rfl hsum).trans (le_of_eq ?_))
  have hp : (∏ c ∈ univ.erase root,
      ENNReal.ofReal (4 * Real.pi * (M * max ‖r c‖ lam) ^ 2)) =
      ENNReal.ofReal (4 * Real.pi * M ^ 2) ^ (Fintype.card ι - 1) *
        ENNReal.ofReal (∏ c ∈ univ.erase root, max ‖r c‖ lam ^ 2) := by
    simp_rw [show ∀ c : ι, 4 * Real.pi * (M * max ‖r c‖ lam) ^ 2 =
      (4 * Real.pi * M ^ 2) * max ‖r c‖ lam ^ 2 by intro c; ring,
      ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * Real.pi * M ^ 2)]
    rw [prod_mul_distrib, prod_const, card_erase_of_mem (mem_univ root), card_univ,
      ENNReal.ofReal_prod_of_nonneg (fun c _ => sq_nonneg _)]
  rw [hp]
  ring

end MultipoleBKT.BadPointTypes

end
