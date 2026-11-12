/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.TreeAssembly
public import MultipoleBKT.Appendix.GeneralExpansion.TreeRoot

/-!
# Tree coordinates with a weighted root

See (A.39). Extend the tree position integration to a nonnegative
measurable root weight. The endpoint cover and its Jacobian-one coordinates
are reused, and the edge minima survive until spatial integration is complete.
-/

@[expose] public section

namespace MultipoleBKT.GeneralExpansion

open MeasureTheory Set Finset SimpleGraph
open scoped ENNReal Classical
open MultipoleIntegral

variable {ι : Type*} [Fintype ι]

/-- Extend a set-root integral bound to every measurable root weight by
nonnegative simple-function approximation. -/
private theorem weighted_integral_le_of_sets {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (e : X → ℂ) (he : Measurable e) (ψ : X → ℝ≥0∞)
    (hψ : Measurable ψ) (K : ℝ≥0∞)
    (hsets : ∀ D : Set ℂ, MeasurableSet D →
      (∫⁻ x, D.indicator (1 : ℂ → ℝ≥0∞) (e x) * ψ x ∂μ) ≤ volume D * K)
    (φ : ℂ → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ x, φ (e x) * ψ x ∂μ) ≤ (∫⁻ t, φ t) * K := by
  refine Measurable.ennreal_induction (motive := fun f : ℂ → ℝ≥0∞ =>
    (∫⁻ x, f (e x) * ψ x ∂μ) ≤ (∫⁻ t, f t) * K) ?_ ?_ ?_ hφ
  · intro c D hD
    have heq : ∀ x, D.indicator (fun _ => c) (e x) * ψ x =
        c * (D.indicator (1 : ℂ → ℝ≥0∞) (e x) * ψ x) := by
      intro x
      by_cases hx : e x ∈ D <;> simp [Set.indicator, hx]
    simp_rw [heq]
    rw [lintegral_const_mul c (f := fun x => D.indicator (1 : ℂ → ℝ≥0∞) (e x) * ψ x)
      (((measurable_one.indicator hD).comp he).fun_mul hψ),
      lintegral_indicator hD, setLIntegral_const]
    calc
      _ ≤ c * (volume D * K) := mul_le_mul' le_rfl (hsets D hD)
      _ = _ := by ring
  · intro f g _ hf hg ihf ihg
    simp only [Pi.add_apply, add_mul]
    rw [lintegral_add_left (f := fun x => f (e x) * ψ x) ((hf.comp he).fun_mul hψ), lintegral_add_left hf]
    rw [add_mul]
    exact add_le_add ihf ihg
  · intro f hf hmono ih
    simp only [ENNReal.iSup_mul]
    rw [lintegral_iSup (f := fun n x => f n (e x) * ψ x)
        (fun n => ((hf n).comp he).fun_mul hψ)
        (fun n m hnm x => mul_le_mul' (hmono hnm (e x)) le_rfl),
      lintegral_iSup hf hmono]
    exact iSup_le fun n => (ih n).trans (mul_le_mul' (le_iSup (fun n => ∫⁻ t, f n t) n) le_rfl)

/-- the actual tree integral for a measurable root weight. The endpoint
cover and coordinate integration are reused through its arbitrary root set. -/
theorem lintegral_connected_positions_tree_le_weighted {M lam : ℝ}
    (hM : 0 ≤ M) (hlam : 0 ≤ lam) (r : ι → ℂ) (root : ι)
    (φ : ℂ → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ y : ι → ℂ, φ (y root) *
      (if (SimpleGraph.fromRel fun i j =>
        MultipoleLinked M lam (y i + r i, y i) (y j + r j, y j)).Connected
        then (1 : ℝ≥0∞) else 0) ≤
      (∫⁻ t, φ t) * ENNReal.ofReal (4 * Real.pi * M ^ 2) ^ (Fintype.card ι - 1) *
        ∑ T ∈ (univ : Finset (SimpleGraph ι)).filter (fun T => T.IsTree),
          ENNReal.ofReal (∏ e ∈ T.edgeFinset,
            edgeMin (fun t => max t lam ^ 2) (fun i => ‖r i‖) e) := by
  let ψ (y : ι → ℂ) := connInd M lam (fun i => (y i + r i, y i))
  have hψ : Measurable ψ := (measurable_connInd M lam).comp (by fun_prop)
  rw [mul_assoc]
  refine (le_of_eq ?_).trans (weighted_integral_le_of_sets volume
    (fun y : ι → ℂ => y root) (measurable_pi_apply root) ψ hψ _ ?_ φ hφ)
  · apply lintegral_congr
    intro y
    congr 1
  · intro D hD
    rw [← mul_assoc]
    have hred := lintegral_connected_positions_tree_le hM hlam r root hD
    refine (le_of_eq ?_).trans hred
    apply lintegral_congr
    intro y
    congr 1
    unfold ψ connInd
    split_ifs <;> rfl

/-- Compatibility form of the spatial bound, obtained from the actual
tree sum by dropping each edge minimum only after its spatial integration. -/
theorem lintegral_connected_positions_root_le_weighted {M lam : ℝ}
    (hM : 0 ≤ M) (hlam : 0 ≤ lam) (φ : ℂ → ℝ≥0∞) (hφ : Measurable φ) (r : ι → ℂ) (root : ι) :
    ∫⁻ y : ι → ℂ, φ (y root) *
      (if (SimpleGraph.fromRel fun i j =>
        MultipoleLinked M lam (y i + r i, y i) (y j + r j, y j)).Connected
        then (1 : ℝ≥0∞) else 0) ≤
      ((Fintype.card ι ^ Fintype.card ι : ℕ) : ℝ≥0∞) * (∫⁻ t, φ t) *
        ∏ c ∈ univ.erase root, ENNReal.ofReal (4 * Real.pi * (M * max ‖r c‖ lam) ^ 2) := by
  have : Nonempty ι := ⟨root⟩
  have hred := lintegral_connected_positions_tree_le_weighted hM hlam r root φ hφ
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

end MultipoleBKT.GeneralExpansion

end
