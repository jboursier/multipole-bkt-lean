/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.SpatialAssembly
import TwoComponentCoulomb.Gibbs.Basic

/-!
# Summing the spatial integrals over actual trees

See (A.6) through
(A.11). The Prüfer theorem counts the trees, with a
separate singleton case.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegral

open MeasureTheory Set Finset SimpleGraph
open scoped ENNReal Classical

variable {ι : Type*} [Fintype ι]

/-- Cayley's count, extended to the unique tree on a singleton. -/
theorem card_trees_eq_pow [Nonempty ι] :
    ((univ : Finset (SimpleGraph ι)).filter (fun T => T.IsTree)).card =
      Fintype.card ι ^ (Fintype.card ι - 2) := by
  by_cases hk : 2 ≤ Fintype.card ι
  · exact card_isTree_eq_pow hk
  · have : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    have hcard : Fintype.card ι = 1 := by simpa using (Fintype.card_le_one_iff_subsingleton.mpr ‹Subsingleton ι› |>.antisymm Fintype.card_pos)
    simp [IsTree.of_subsingleton, hcard]

/-- Integrate the spanning-tree union bound, preserving the minimum of
the two endpoint radii on every edge. -/
theorem lintegral_connected_positions_tree_le {M lam : ℝ}
    (hM : 0 ≤ M) (hlam : 0 ≤ lam) (r : ι → ℂ) (root : ι)
    {D : Set ℂ} (hD : MeasurableSet D) :
    ∫⁻ y : ι → ℂ, D.indicator (1 : ℂ → ℝ≥0∞) (y root) *
      (if (SimpleGraph.fromRel fun i j =>
        MultipoleLinked M lam (y i + r i, y i) (y j + r j, y j)).Connected
        then (1 : ℝ≥0∞) else 0) ≤
      volume D * ENNReal.ofReal (4 * Real.pi * M ^ 2) ^ (Fintype.card ι - 1) *
        ∑ T ∈ (univ : Finset (SimpleGraph ι)).filter (fun T => T.IsTree),
          ENNReal.ofReal (∏ e ∈ T.edgeFinset,
            edgeMin (fun t => max t lam ^ 2) (fun i => ‖r i‖) e) := by
  classical
  let G (y : ι → ℂ) := SimpleGraph.fromRel fun i j =>
    MultipoleLinked M lam (y i + r i, y i) (y j + r j, y j)
  let W (T : SimpleGraph ι) (y : ι → ℂ) := D.indicator (1 : ℂ → ℝ≥0∞) (y root) *
    ∏ e ∈ T.edgeFinset, (if e ∈ (G y).edgeSet then (1 : ℝ≥0∞) else 0)
  have hW : ∀ T, Measurable (W T) := by
    intro T
    refine ((measurable_const.indicator hD).comp (measurable_pi_apply root)).mul ?_
    apply Finset.measurable_prod
    intro e _
    exact (Measurable.ite (measurableSet_setOf_fromRel_multipoleLinked M lam
      (fun H : SimpleGraph ι => e ∈ H.edgeSet)) measurable_const measurable_const).comp
        (f := fun y : ι → ℂ => fun i => (y i + r i, y i)) (by fun_prop)
  calc
    _ ≤ ∫⁻ y : ι → ℂ, ∑ T ∈ (univ : Finset (SimpleGraph ι)).filter (fun T => T.IsTree),
        W T y := by
      apply lintegral_mono
      intro y
      dsimp only [W]
      rw [← mul_sum]
      apply mul_le_mul' le_rfl
      have ht := connectedIndicator_le_sum_trees (G y)
      convert ht using 1
      · split_ifs <;> rfl
      · apply sum_congr rfl
        intro T _
        apply prod_congr rfl
        intro e _
        split_ifs <;> rfl
    _ = ∑ T ∈ (univ : Finset (SimpleGraph ι)).filter (fun T => T.IsTree),
        ∫⁻ y, W T y := lintegral_finsetSum _ (fun T _ => hW T)
    _ ≤ ∑ T ∈ (univ : Finset (SimpleGraph ι)).filter (fun T => T.IsTree),
        volume D * ENNReal.ofReal (4 * Real.pi * M ^ 2) ^ (Fintype.card ι - 1) *
          ENNReal.ofReal (∏ e ∈ T.edgeFinset,
            edgeMin (fun t => max t lam ^ 2) (fun i => ‖r i‖) e) := by
      apply sum_le_sum
      intro T hT
      exact lintegral_tree_positions_le (mem_filter.mp hT).2 root hM hlam r hD
    _ = _ := (mul_sum _ _ _).symm

/-- Compatibility form of the spatial bound, obtained from the actual
tree sum by dropping each edge minimum only after its spatial integration. -/
theorem lintegral_connected_positions_root_le {M lam : ℝ}
    (hM : 0 ≤ M) (hlam : 0 ≤ lam) (N : ℕ) (r : ι → ℂ) (root : ι) :
    ∫⁻ y : ι → ℂ, (TwoComponentCoulomb.box N).indicator (1 : ℂ → ℝ≥0∞) (y root) *
      (if (SimpleGraph.fromRel fun i j =>
        MultipoleLinked M lam (y i + r i, y i) (y j + r j, y j)).Connected
        then (1 : ℝ≥0∞) else 0) ≤
      ((Fintype.card ι ^ Fintype.card ι : ℕ) : ℝ≥0∞) * (N : ℝ≥0∞) *
        ∏ c ∈ univ.erase root, ENNReal.ofReal (4 * Real.pi * (M * max ‖r c‖ lam) ^ 2) := by
  have : Nonempty ι := ⟨root⟩
  have hred := lintegral_connected_positions_tree_le hM hlam r root
    (TwoComponentCoulomb.measurableSet_box N)
  rw [TwoComponentCoulomb.volume_box] at hred
  have hsum : (∑ T ∈ (univ : Finset (SimpleGraph ι)).filter (fun T => T.IsTree),
      ENNReal.ofReal (∏ e ∈ T.edgeFinset,
        edgeMin (fun t => max t lam ^ 2) (fun i => ‖r i‖) e)) ≤
      ((Fintype.card ι ^ Fintype.card ι : ℕ) : ℝ≥0∞) *
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
      _ ≤ _ := by
        rw [sum_const, nsmul_eq_mul, card_trees_eq_pow]
        apply mul_le_mul' _ le_rfl
        exact_mod_cast (show Fintype.card ι ^ (Fintype.card ι - 2) ≤
          Fintype.card ι ^ Fintype.card ι by gcongr; omega)
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

end MultipoleBKT.MultipoleIntegral

end
