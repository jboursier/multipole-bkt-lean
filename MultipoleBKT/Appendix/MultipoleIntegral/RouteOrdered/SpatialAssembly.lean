/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.EdgeIndex
public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.Spatial
public import MultipoleBKT.Gibbs.Activities

/-!
# Endpoint sums and the spatial tree integral

See (A.8) through
(A.11). Expand the finite endpoint assignment sum before
integrating in tree coordinates. The edge minimum is retained throughout.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegral

open MeasureTheory Set Finset SimpleGraph
open scoped ENNReal Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Each endpoint-cell summand is measurable, including the cell boundary. -/
theorem measurable_endpointLinkWeight (M lam : ℝ) (l : Fin 4) :
    Measurable (fun p : (ℂ × ℂ) × (ℂ × ℂ) => endpointLinkWeight M lam l p.1 p.2) :=
  (Measurable.ite (measurableSet_multipoleLinked M lam) measurable_const measurable_const).indicator
    (measurableSet_endpointCell l)

/-- Integrate the endpoint cover along an oriented tree. There are four
choices per non-root child, with no extra choice at the root. -/
theorem lintegral_links_parent_le {root : ι} {par : ι → ι}
    (hpar : IsParentMap root par) (M lam : ℝ) (r : ι → ℂ)
    {D : Set ℂ} (hD : MeasurableSet D) :
    ∫⁻ y : ι → ℂ, D.indicator (1 : ℂ → ℝ≥0∞) (y root) *
      ∏ c ∈ univ.erase root,
        (if MultipoleLinked M lam (y c + r c, y c)
          (y (par c) + r (par c), y (par c)) then (1 : ℝ≥0∞) else 0) ≤
      (4 : ℝ≥0∞) ^ (Fintype.card ι - 1) *
        (volume D * ∏ c ∈ univ.erase root, volume (Metric.closedBall (0 : ℂ)
          (M * min (max ‖r c‖ lam) (max ‖r (par c)‖ lam)))) := by
  let C := {c : ι // c ≠ root}
  let W (l : C → Fin 4) (y : ι → ℂ) := D.indicator (1 : ℂ → ℝ≥0∞) (y root) *
    ∏ c : C, endpointLinkWeight M lam (l c) (y c + r c, y c)
      (y (par c) + r (par c), y (par c))
  have hW : ∀ l, Measurable (W l) := by
    intro l
    refine ((measurable_const.indicator hD).comp (measurable_pi_apply root)).mul ?_
    apply Finset.measurable_prod
    intro c _
    exact (measurable_endpointLinkWeight M lam (l c)).comp
      (f := fun y : ι → ℂ => ((y c + r c, y c),
        (y (par c) + r (par c), y (par c)))) (by fun_prop)
  have hprod (f : ι → ℝ≥0∞) : ∏ c ∈ univ.erase root, f c = ∏ c : C, f c :=
    Finset.prod_subtype (p := fun c => c ≠ root) (univ.erase root) (by simp) f
  have hbound : ∀ l, ∫⁻ y, W l y ≤ volume D *
      ∏ c ∈ univ.erase root, volume (Metric.closedBall (0 : ℂ)
        (M * min (max ‖r c‖ lam) (max ‖r (par c)‖ lam))) := by
    intro l
    let l' (c : ι) : Fin 4 := if hc : c ≠ root then l ⟨c, hc⟩ else 0
    have heq : W l = fun y : ι → ℂ => D.indicator (1 : ℂ → ℝ≥0∞) (y root) *
        ∏ c ∈ univ.erase root, endpointLinkWeight M lam (l' c) (y c + r c, y c)
          (y (par c) + r (par c), y (par c)) := by
      funext y
      rw [hprod]
      dsimp only [W]
      congr 1
      apply prod_congr rfl
      intro c _
      simp only [l', dite_eq_left c.2]
      rfl
    rw [heq]
    exact lintegral_endpointCell_tree_le hpar M lam r l' hD
  calc
    _ ≤ ∫⁻ y : ι → ℂ, ∑ l : C → Fin 4, W l y := by
      apply lintegral_mono
      intro y
      dsimp only [W]
      rw [hprod, ← mul_sum]
      rw [← Fintype.prod_sum (fun (c : C) (l : Fin 4) => endpointLinkWeight M lam l
        (y c + r c, y c) (y (par c) + r (par c), y (par c)))]
      apply mul_le_mul' le_rfl
      exact prod_le_prod fun c _ => linkedIndicator_le_sum_endpointLinkWeight M lam _ _
    _ = ∑ l : C → Fin 4, ∫⁻ y, W l y := lintegral_finsetSum _ (fun l _ => hW l)
    _ ≤ ∑ _l : C → Fin 4, volume D *
        ∏ c ∈ univ.erase root, volume (Metric.closedBall (0 : ℂ)
          (M * min (max ‖r c‖ lam) (max ‖r (par c)‖ lam))) :=
      sum_le_sum fun l _ => hbound l
    _ = _ := by
      rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat]
      have hc : Fintype.card C = Fintype.card ι - 1 := by
        have h := Cayley.card_subtype_ne_add_one root
        dsimp only [C]
        have : Fintype.card {i // i ≠ root} + 1 = Fintype.card ι := by
          simpa only [← Nat.card_eq_fintype_card] using h
        omega
      rw [hc]

/-- The spatial integral for one actual tree, after the endpoint cover
and its measure-preserving coordinate change. -/
theorem lintegral_tree_positions_le {T : SimpleGraph ι} (hT : T.IsTree)
    (root : ι) {M lam : ℝ} (hM : 0 ≤ M) (_hlam : 0 ≤ lam) (r : ι → ℂ)
    {D : Set ℂ} (hD : MeasurableSet D) :
    ∫⁻ y : ι → ℂ, D.indicator (1 : ℂ → ℝ≥0∞) (y root) *
      ∏ e ∈ T.edgeFinset,
        (if e ∈ (SimpleGraph.fromRel fun i j =>
          MultipoleLinked M lam (y i + r i, y i) (y j + r j, y j)).edgeSet
          then (1 : ℝ≥0∞) else 0) ≤
      volume D * ENNReal.ofReal (4 * Real.pi * M ^ 2) ^ (Fintype.card ι - 1) *
        ENNReal.ofReal (∏ e ∈ T.edgeFinset,
          edgeMin (fun t => max t lam ^ 2) (fun i => ‖r i‖) e) := by
  obtain ⟨par, hpar, hadj⟩ := exists_parent_of_connected hT.connected root
  have heq (y : ι → ℂ) : (∏ e ∈ T.edgeFinset,
      if e ∈ (SimpleGraph.fromRel fun i j =>
        MultipoleLinked M lam (y i + r i, y i) (y j + r j, y j)).edgeSet
        then (1 : ℝ≥0∞) else 0) =
      ∏ c ∈ univ.erase root, (if MultipoleLinked M lam (y c + r c, y c)
        (y (par c) + r (par c), y (par c)) then (1 : ℝ≥0∞) else 0) := by
    rw [prod_edges_eq_prod_children hT hpar hadj]
    apply prod_congr rfl
    intro c hc
    have hne := (hadj c (mem_erase.mp hc).1).ne
    simp only [mem_edgeSet, fromRel_adj, Multipole.multipoleLinked_comm, or_self]
    exact if_congr (and_iff_right hne) rfl rfl
  simp_rw [heq]
  refine (lintegral_links_parent_le hpar M lam r hD).trans (le_of_eq ?_)
  have hball (c : ι) : volume (Metric.closedBall (0 : ℂ)
      (M * min (max ‖r c‖ lam) (max ‖r (par c)‖ lam))) =
      ENNReal.ofReal (Real.pi * M ^ 2) *
        ENNReal.ofReal (max (min ‖r c‖ ‖r (par c)‖) lam ^ 2) := by
    have hmin : 0 ≤ min (max ‖r c‖ lam) (max ‖r (par c)‖ lam) := by positivity
    rw [Complex.volume_closedBall, ← ENNReal.ofReal_pow (mul_nonneg hM hmin),
      ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [mul_pow, max_min_distrib_right]
    ring
  simp_rw [hball]
  rw [prod_mul_distrib, prod_const, card_erase_of_mem (mem_univ root), card_univ,
    ← ENNReal.ofReal_prod_of_nonneg (fun c _ => sq_nonneg _)]
  have hp := prod_edges_eq_prod_children hT hpar hadj
      (edgeMin (fun t => max t lam ^ 2) (fun i => ‖r i‖))
  simp only [edgeMin_mk] at hp
  rw [← hp]
  rw [show ENNReal.ofReal (4 * Real.pi * M ^ 2) =
      4 * ENNReal.ofReal (Real.pi * M ^ 2) by
    rw [show 4 * Real.pi * M ^ 2 = 4 * (Real.pi * M ^ 2) by ring,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat], mul_pow]
  ring

end MultipoleBKT.MultipoleIntegral

end
