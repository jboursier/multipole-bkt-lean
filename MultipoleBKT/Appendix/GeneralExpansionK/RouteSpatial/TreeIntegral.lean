/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.MarkedEdge
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.EvenTree

/-!
# Weighted tree integration with a marked even edge

See (A.62) and Step 3 of the proof of Lemma A.7. Apply the endpoint tree coordinates to the same selected
tree, retain its root weight, and integrate the marked edge separately.
The two endpoint squares are allocated by ordering the two trees left by
deleting the marked edge.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset SimpleGraph Limits Peeling SmallIntegral
open SmallIntegral.RouteJ SmallIntegral.RouteJext
open scoped Classical ENNReal

/-- Endpoint coordinates for arbitrary measurable scalar factors on the
edges of the selected tree. The root weight is integrated independently. -/
theorem lintegral_tree_product_le {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) (root : V) (u : V → ℂ)
    (H : ℂ → ℝ≥0∞) (hH : Measurable H) (f : Sym2 V → ℝ → ℝ≥0∞)
    (hf : ∀ e, Measurable (f e)) :
    (∫⁻ x : V → ℂ, H (x root) * ∏ e ∈ T.edgeFinset,
      f e (dipoleDistOn (ofPosVec x u) e)) ≤
      (4 : ℝ≥0∞) ^ (Fintype.card V - 1) *
        ((∫⁻ t, H t) * ∏ e ∈ T.edgeFinset, ∫⁻ z : ℂ, f e ‖z‖) := by
  obtain ⟨par, hpar, hinj, himg⟩ := exists_parent_of_isTree hT root
  let I := {i : V // i ≠ root}
  have hp (x : V → ℂ) : (∏ e ∈ T.edgeFinset, f e (dipoleDistOn (ofPosVec x u) e)) =
      ∏ i : I, f s(i.val, par i.val) (dipoleDist (ofPosVec x u i) (ofPosVec x u (par i))) := by
    rw [← himg, prod_image hinj]
    exact prod_subtype (univ.erase root) (p := fun i => i ≠ root) (by simp) _
  have hp' : (∏ e ∈ T.edgeFinset, ∫⁻ z : ℂ, f e ‖z‖) =
      ∏ i : I, ∫⁻ z : ℂ, f s(i.val, par i.val) ‖z‖ := by
    rw [← himg, prod_image hinj]
    exact prod_subtype (univ.erase root) (p := fun i => i ≠ root) (by simp) _
  simp_rw [hp]
  rw [hp']
  have hc : Fintype.card {i : V // i ≠ root} = Fintype.card V - 1 := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_subtype_eq]
  simpa only [hc] using lintegral_endpoint_product_le root par (fun i => T.dist i root)
    (fun i hi => (hpar i hi).2) u H hH
    (fun i : I => f s(i.val, par i.val)) (fun i => hf _)

/-- The marked even edge and every other edge of the cutoff tree retain
one logarithm. The root can be the screening gain or the bad-root indicator. -/
theorem lintegral_marked_tree_weighted_le {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {M lam h : ℝ} (hM : 1 ≤ M) (hlam : 0 < lam) (u : V → ℂ)
    (hu : ∀ i, rho lam (u i) ≤ h) (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree)
    (A E : Finset (Sym2 V)) (mark : Sym2 V) (root : V)
    (H : ℂ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ x : V → ℂ, H (x root) * ∏ e ∈ T.edgeFinset,
      ENNReal.ofReal (markedCutProfile A E mark M lam h u e (dipoleDistOn (ofPosVec x u) e))) ≤
      (∫⁻ t, H t) * ENNReal.ofReal
        ((4 * Real.pi * (M ^ 2 + 5)) ^ (Fintype.card V - 1) *
          (1 + Real.log (17 * h / minRho lam u)) ^ (Fintype.card V - 1)) := by
  have hb := lintegral_tree_product_le T hT root u H hH
    (fun e d => ENNReal.ofReal (markedCutProfile A E mark M lam h u e d))
    (fun e => (measurable_markedCutProfile A E mark M lam h u e).ennreal_ofReal)
  let C := Real.pi * (M ^ 2 + 5)
  let L := 1 + Real.log (17 * h / minRho lam u)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hL : 0 ≤ L := by
    obtain ⟨i⟩ := ‹Nonempty V›
    have ha := minRho_pos hlam u
    have hah := (minRho_le_rho lam u i).trans (hu i)
    have := Real.log_nonneg ((one_le_div ha).2 (show minRho lam u ≤ 17 * h by linarith))
    dsimp only [L]
    linarith
  have hcount : T.edgeFinset.card = Fintype.card V - 1 := by
    have := hT.card_edgeFinset
    omega
  have hi : (∏ e ∈ T.edgeFinset,
      ∫⁻ z : ℂ, ENNReal.ofReal (markedCutProfile A E mark M lam h u e ‖z‖)) ≤
      ENNReal.ofReal (C * L) ^ (Fintype.card V - 1) := by
    calc
      _ ≤ ∏ _e ∈ T.edgeFinset, ENNReal.ofReal (C * L) := prod_le_prod fun e _ =>
        lintegral_markedCutProfile_le A E mark hM hlam u hu e
      _ = _ := by rw [prod_const, hcount]
  refine hb.trans ((mul_le_mul' le_rfl (mul_le_mul' le_rfl hi)).trans_eq ?_)
  rw [← ENNReal.ofReal_pow (mul_nonneg hC hL),
    show (4 : ℝ≥0∞) ^ (Fintype.card V - 1) = ENNReal.ofReal ((4 : ℝ) ^ (Fintype.card V - 1)) by
      rw [ENNReal.ofReal_pow (by norm_num)]; norm_num]
  rw [mul_left_comm, mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  dsimp only [C, L]
  simp only [mul_pow]
  ring

/-- After deleting the marked edge, tree ordering on both parts absorbs
both endpoint squares. This is the full product in (A.62). -/
theorem marked_radius_allocation {V : Type*} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} (hT : T.IsTree) {i j : V} (hij : T.Adj i j)
    (r : V → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    max (r i) lam ^ 2 * max (r j) lam ^ 2 *
      (∏ e ∈ T.edgeFinset.erase s(i,j), edgeMin (fun a => max a lam ^ 2) r e) ≤
        ∏ v, max (r v) lam ^ 2 := by
  exact RouteCases.marked_tree_radius_allocation hT hij r (fun a => max a lam ^ 2)
    (fun _ _ h => pow_le_pow_left₀ (hlam.le.trans (le_max_right _ _)) (max_le_max h le_rfl) 2)
    (fun _ => sq_nonneg _)

end MultipoleBKT.ExpansionK.RouteSpatial

end
