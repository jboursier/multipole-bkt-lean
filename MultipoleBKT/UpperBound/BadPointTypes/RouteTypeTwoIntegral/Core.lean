/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeTwoIntegral.Pruning
public import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeTwoIntegral.Spatial

/-!
# Ordered integration of the core left by leaf deletion

The paper: (5.138)
and (5.140). First integrate deleted leaves. Then
sum over the largest radius of the terminal tree and use the ordered radial
nested integral. The cutoff is dropped only for that terminal integral.
-/

@[expose] public section

namespace MultipoleBKT.BadPointTypes

open MeasureTheory Finset MultipoleIntegral Set
open scoped ENNReal Classical

variable {χ : ℂ → ℝ} {β lam M : ℝ}
variable {V : Type*} [Fintype V]

/-- The ordered integral of a `k`-vertex core, including angular and kernel factors. -/
noncomputable def orderedCoreBound (χ : ℂ → ℝ) (β lam : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (β * kernelConst χ)) ^ k *
    ((k : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi) ^ k *
      orderedRadial β lam (Ioi 0) (k - 1))

/-- All retained cutoff factors belong to the radial tree integral. -/
theorem radialCut_mul_treeDipoleWeight (T : SimpleGraph V) (h : ℝ) (r : V → ℂ) :
    radialCut h r * treeDipoleWeight T χ β lam r =
      ENNReal.ofReal (∏ e ∈ T.edgeFinset,
        edgeMin (fun t => max t lam ^ 2) (fun i => ‖r i‖) e) *
          ∏ i, cutFactor χ β lam h (r i) := by
  unfold radialCut treeDipoleWeight
  by_cases hr : ∀ i, ‖r i‖ ≤ h
  · rw [ite_eq_left hr, one_mul]
    congr 1
    apply prod_congr rfl
    intro i _
    symm
    apply Set.indicator_of_mem
    simpa only [Metric.mem_closedBall, dist_zero_right] using hr i
  · obtain ⟨i, hi⟩ := not_forall.mp hr
    have hz : cutFactor χ β lam h (r i) = 0 := by
      apply Set.indicator_of_notMem
      simpa only [Metric.mem_closedBall, dist_zero_right] using hi
    rw [ite_eq_right hr, zero_mul, prod_eq_zero (mem_univ i) hz, mul_zero]

/-- Ordered integration on the terminal tree. No ordering constraint from
removed vertices is imposed on this core. -/
theorem radialTreeIntegral_core_le {T : SimpleGraph V} (hT : T.IsTree)
    [Nonempty V] (hχ : IsMollifier χ) (hlam : 0 < lam) (hβ : 0 ≤ β) (h : ℝ) :
    radialTreeIntegral T lam (cutFactor χ β lam h) ≤
      orderedCoreBound χ β lam (Fintype.card V) := by
  have hpt (r : V → ℂ) : ENNReal.ofReal (∏ e ∈ T.edgeFinset,
      edgeMin (fun t => max t lam ^ 2) (fun i => ‖r i‖) e) *
        ∏ i, cutFactor χ β lam h (r i) ≤ treeDipoleWeight T χ β lam r := by
    apply mul_le_mul' le_rfl
    exact prod_le_prod fun i _ => Set.indicator_le_self _ _ _
  exact (lintegral_mono hpt).trans (lintegral_tree_smoothed_infinite_le hT hχ hlam hβ)

/-- Leaf deletion to `k` vertices followed by the ordered integral of exactly
that remaining tree. The existential witness records which core was integrated. -/
theorem pruned_core_ordered_bound {T : SimpleGraph V} (hT : T.IsTree)
    {k : ℕ} (hk : 1 ≤ k) (hkV : k ≤ Fintype.card V)
    (hχ : IsMollifier χ) (hlam : 0 < lam) (hβ : 0 ≤ β) (h : ℝ) :
    ∃ (W : Type _) (_ : Fintype W) (U : SimpleGraph W),
      LeafPruning T U ∧ Fintype.card W = k ∧ U.IsTree ∧
        radialTreeIntegral T lam (cutFactor χ β lam h) ≤
          (∫⁻ z : ℂ, ENNReal.ofReal (max ‖z‖ lam ^ 2) * cutFactor χ β lam h z) ^
            (Fintype.card V - k) * orderedCoreBound χ β lam k := by
  obtain ⟨W, hW, U, hchain, hsize, hU, hb⟩ :=
    exists_pruned_core hT hk hkV hlam (measurable_cutFactor hχ hlam β h)
  have : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  refine ⟨W, hW, U, hchain, hsize, hU, hb.trans ?_⟩
  apply mul_le_mul' le_rfl
  simpa only [hsize] using radialTreeIntegral_core_le hU hχ hlam hβ h

/-- The type-two spatial integral after leaf removal and ordered core integration.
Cayley's count and the endpoint factor are kept explicit. -/
theorem lintegral_blockWeight_cut_le_ordered [Nonempty V]
    (hχ : IsMollifier χ) (hlam : 0 < lam) (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (h : ℝ) (N : ℕ) {k : ℕ} (hk : 1 ≤ k) (hkV : k ≤ Fintype.card V) :
    ∫⁻ c : V → ℂ × ℂ, blockWeight M lam (cutDipoleWeight χ β lam h N) c ≤
      (N : ℝ≥0∞) * ENNReal.ofReal (4 * Real.pi * M ^ 2) ^ (Fintype.card V - 1) *
        ((Fintype.card V ^ (Fintype.card V - 2) : ℕ) : ℝ≥0∞) *
          ((∫⁻ z : ℂ, ENNReal.ofReal (max ‖z‖ lam ^ 2) * cutFactor χ β lam h z) ^
            (Fintype.card V - k) * orderedCoreBound χ β lam k) := by
  refine (lintegral_blockWeight_cut_tree_le hχ hlam hM h N).trans ?_
  have hsum : (∑ T ∈ (univ : Finset (SimpleGraph V)).filter (fun T => T.IsTree),
      ∫⁻ r : V → ℂ, radialCut h r * treeDipoleWeight T χ β lam r) ≤
      ((Fintype.card V ^ (Fintype.card V - 2) : ℕ) : ℝ≥0∞) *
        ((∫⁻ z : ℂ, ENNReal.ofReal (max ‖z‖ lam ^ 2) * cutFactor χ β lam h z) ^
          (Fintype.card V - k) * orderedCoreBound χ β lam k) := by
    calc
      _ ≤ ∑ _T ∈ (univ : Finset (SimpleGraph V)).filter (fun T => T.IsTree),
          (∫⁻ z : ℂ, ENNReal.ofReal (max ‖z‖ lam ^ 2) * cutFactor χ β lam h z) ^
            (Fintype.card V - k) * orderedCoreBound χ β lam k := by
        apply sum_le_sum
        intro T hT
        obtain ⟨W, hW, U, _, _, _, hb⟩ := pruned_core_ordered_bound
          (mem_filter.mp hT).2 hk hkV hχ hlam hβ h
        simpa only [radialCut_mul_treeDipoleWeight, radialTreeIntegral] using hb
      _ = _ := by rw [sum_const, nsmul_eq_mul, card_trees_eq_pow]
  exact (mul_le_mul' le_rfl hsum).trans (le_of_eq (by ring))

end MultipoleBKT.BadPointTypes

end
