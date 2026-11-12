/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.Coordinates
public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.Endpoints

/-!
# Spatial integration on an endpoint-realization cell

See (A.8) through
(A.11). Fix the tree and the realization on every edge.
On that cell each selected coordinate lies in a disc. Drop the remaining
cell constraints and apply the measure-preserving tree coordinate map.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegral

open MeasureTheory Set Finset
open scoped ENNReal Classical

/-- The link indicator restricted to one of the four endpoint cells. -/
noncomputable def endpointLinkWeight (M lam : ℝ) (l : Fin 4)
    (d e : ℂ × ℂ) : ℝ≥0∞ :=
  (endpointCell l).indicator
    (fun p => if MultipoleLinked M lam p.1 p.2 then 1 else 0) (d, e)

/-- After fixing the endpoint cell, the link indicator is bounded by a
single disc indicator in the selected difference coordinate. -/
theorem endpointLinkWeight_le (M lam : ℝ) (l : Fin 4) (d e : ℂ × ℂ) :
    endpointLinkWeight M lam l d e ≤
      (Metric.closedBall (0 : ℂ)
        (M * min (max ‖d.1 - d.2‖ lam) (max ‖e.1 - e.2‖ lam))).indicator
          (1 : ℂ → ℝ≥0∞) (endpointDifference d e l) := by
  classical
  unfold endpointLinkWeight
  by_cases hc : (d, e) ∈ endpointCell l
  · rw [indicator_of_mem hc]
    by_cases hl : MultipoleLinked M lam d e
    · rw [ite_eq_left hl, indicator_of_mem]
      · rfl
      · rw [Metric.mem_closedBall, dist_zero_right]
        exact (endpointCell_linked_iff hc).mp hl
    · rw [ite_eq_right hl]
      exact zero_le
  · rw [indicator_of_notMem hc]
    exact zero_le

/-- The link union bound with the endpoint realization still visible.
This supplies the single-edge step of (A.8). -/
theorem linkedIndicator_le_sum_endpointLinkWeight (M lam : ℝ) (d e : ℂ × ℂ) :
    (if MultipoleLinked M lam d e then (1 : ℝ≥0∞) else 0) ≤
      ∑ l : Fin 4, endpointLinkWeight M lam l d e := by
  classical
  by_cases h : MultipoleLinked M lam d e
  · rw [ite_eq_left h]
    refine (one_le_sum_endpointCells d e).trans (le_of_eq ?_)
    apply sum_congr rfl
    intro l _
    by_cases hc : (d, e) ∈ endpointCell l <;> simp [endpointLinkWeight, hc, h]
  · rw [ite_eq_right h]
    exact zero_le

/-- The spatial estimate (A.11) for a fixed endpoint assignment. The
root can be restricted to any measurable set, including a bad-point
neighborhood. No disjointness assumption on endpoint cells is used. -/
theorem lintegral_endpointCell_tree_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {root : ι} {par : ι → ι} (hpar : IsParentMap root par)
    (M lam : ℝ) (r : ι → ℂ) (l : ι → Fin 4) {D : Set ℂ} (hD : MeasurableSet D) :
    ∫⁻ y : ι → ℂ, D.indicator (1 : ℂ → ℝ≥0∞) (y root) *
      ∏ c ∈ univ.erase root,
        endpointLinkWeight M lam (l c) (y c + r c, y c) (y (par c) + r (par c), y (par c)) ≤
      volume D * ∏ c ∈ univ.erase root,
        volume (Metric.closedBall (0 : ℂ)
          (M * min (max ‖r c‖ lam) (max ‖r (par c)‖ lam))) := by
  let ρ (c : ι) := M * min (max ‖r c‖ lam) (max ‖r (par c)‖ lam)
  let f (c : ι) := (Metric.closedBall (0 : ℂ) (ρ c)).indicator (1 : ℂ → ℝ≥0∞)
  have hf : ∀ c, Measurable (f c) := fun c => measurable_const.indicator measurableSet_closedBall
  calc
    _ ≤ ∫⁻ y : ι → ℂ, D.indicator (1 : ℂ → ℝ≥0∞) (y root) *
        ∏ c ∈ univ.erase root,
          f c (y c - y (par c) + endpointOffset (r c) (r (par c)) (l c)) := by
      apply lintegral_mono
      intro y
      refine mul_le_mul' le_rfl (prod_le_prod fun c _ => ?_)
      have h := endpointLinkWeight_le M lam (l c) (y c + r c, y c)
        (y (par c) + r (par c), y (par c))
      simpa only [add_sub_cancel_left, endpointDifference_eq] using h
    _ = _ := by
      rw [lintegral_treeCoordinates_prod hpar (fun c => endpointOffset (r c) (r (par c)) (l c))
        (D.indicator (1 : ℂ → ℝ≥0∞)) (measurable_const.indicator hD) f hf,
        lintegral_indicator_one hD]
      congr 1
      exact prod_congr rfl fun c _ => lintegral_indicator_one measurableSet_closedBall

end MultipoleBKT.MultipoleIntegral

end
