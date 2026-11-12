/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.Cayley
public import MultipoleBKT.Appendix.OrderingTree
public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.Endpoints

/-!
# Tree union and largest-radius decomposition

See (A.6) and (A.12). A connected linking graph contains a
spanning tree. The Prüfer count supplies the number of trees. After
integrating positions, choose a largest radius and apply the leaf-induction
ordering lemma. Ties are covered by the finite sum over all maxima.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegral

open MeasureTheory Finset Set SimpleGraph
open scoped ENNReal Classical

variable {ι : Type*} [Fintype ι]

/-- The spanning-tree union bound underlying (A.6). -/
theorem connectedIndicator_le_sum_trees (G : SimpleGraph ι) :
    (if G.Connected then (1 : ℝ≥0∞) else 0) ≤
      ∑ T ∈ (univ : Finset (SimpleGraph ι)).filter (fun T => T.IsTree),
        ∏ e ∈ T.edgeFinset, (if e ∈ G.edgeSet then (1 : ℝ≥0∞) else 0) := by
  by_cases hG : G.Connected
  · rw [ite_eq_left hG]
    obtain ⟨T, hTG, hT⟩ := hG.exists_isTree_le
    have hprod : (∏ e ∈ T.edgeFinset,
        if e ∈ G.edgeSet then (1 : ℝ≥0∞) else 0) = 1 := by
      apply prod_eq_one
      intro e he
      rw [ite_eq_left]
      exact edgeSet_mono hTG (mem_edgeFinset.mp he)
    calc
      (1 : ℝ≥0∞) = _ := hprod.symm
      _ ≤ _ := Finset.single_le_sum (f := fun H : SimpleGraph ι =>
        ∏ e ∈ H.edgeFinset, if e ∈ G.edgeSet then (1 : ℝ≥0∞) else 0)
        (fun _ _ => zero_le) (mem_filter.mpr ⟨Finset.mem_univ T, hT⟩)
  · rw [ite_eq_right hG]
    exact zero_le

variable [DecidableEq ι]

/-- The regularized edge product in (A.11) is controlled by the product
over all non-root vertices, as stated just before (A.13). -/
theorem tree_radius_product_le {T : SimpleGraph ι} (hT : T.IsTree)
    {lam : ℝ} (hlam : 0 ≤ lam) (r : ι → ℝ) (root : ι) (hroot : ∀ i, r i ≤ r root) :
    ∏ e ∈ T.edgeFinset, edgeMin (fun t => max t lam ^ 2) r e ≤
      ∏ i ∈ univ.erase root, max (r i) lam ^ 2 := by
  apply ordering_tree hT _ (fun _ => sq_nonneg _) r root hroot
  intro a b hab
  exact pow_le_pow_left₀ (le_max_of_le_right hlam) (max_le_max hab le_rfl) 2

/-- The pointwise largest-radius split (A.12), followed by the ordering
lemma. Every configuration belongs to at least one maximum cell. -/
theorem tree_radius_weight_le_sum_ordered [Nonempty ι] {T : SimpleGraph ι}
    (hT : T.IsTree) {lam : ℝ} (hlam : 0 ≤ lam) (r : ι → ℝ) (w : ι → ℝ≥0∞) :
    ENNReal.ofReal (∏ e ∈ T.edgeFinset, edgeMin (fun t => max t lam ^ 2) r e) * ∏ i, w i ≤
      ∑ root : ι, (if ∀ i, r i ≤ r root then (1 : ℝ≥0∞) else 0) *
        (ENNReal.ofReal (∏ i ∈ univ.erase root, max (r i) lam ^ 2) * ∏ i, w i) := by
  obtain ⟨root, hroot⟩ := Finite.exists_max r
  calc
    _ ≤ ENNReal.ofReal (∏ i ∈ univ.erase root, max (r i) lam ^ 2) * ∏ i, w i := by
      gcongr
      exact tree_radius_product_le hT hlam r root hroot
    _ = (if ∀ i, r i ≤ r root then (1 : ℝ≥0∞) else 0) *
        (ENNReal.ofReal (∏ i ∈ univ.erase root, max (r i) lam ^ 2) * ∏ i, w i) := by
      rw [ite_eq_left hroot, one_mul]
    _ ≤ _ := Finset.single_le_sum (f := fun root : ι =>
      (if ∀ i, r i ≤ r root then (1 : ℝ≥0∞) else 0) *
        (ENNReal.ofReal (∏ i ∈ univ.erase root, max (r i) lam ^ 2) * ∏ i, w i))
      (fun _ _ => zero_le) (mem_univ root)

end MultipoleBKT.MultipoleIntegral

end
