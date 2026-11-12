/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Quadratic.RouteLift.Balance

/-!
# Heavy-light compensation on the bridge-tree

The paper: Corollary 5.34. Retain the leaf marks, transport their denominators to the
last bridge attachments, separate the parent and heavy-child radii there,
and multiply the resulting block estimates.
-/

@[expose] public section

open Finset SimpleGraph
open scoped Classical

namespace MultipoleBKT.UpperBound.Quadratic
open CoreForest RouteLift

variable {Λ V : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype V] [DecidableEq V]
  {τ : SimpleGraph Λ} [DecidableRel τ.Adj] {a : Λ} {T : SimpleGraph V}


/-- Step 4 of Corollary 5.34, the paper:
transport along the edge-disjoint lifted paths before radius compensation.
The accumulated exponent is their total length in the extracted tree. -/
theorem lifted_bridge_bound_length (D : BlockTree τ a T) (hτ : τ.IsTree) (hT : T.IsTree)
    (ha : τ.degree a = 1) {r δ : V → ℝ} {R W : Λ → ℝ} {K : ℝ}
    (hr : ∀ S, 0 ≤ r S) (hδ : ∀ S, 0 < δ S) (hrδ : ∀ S, r S ≤ δ S)
    (hR : ∀ u, 0 ≤ R u) (hrR : ∀ S, r S ≤ R (D.block S))
    (hK : 1 ≤ K) (hW : ∀ u, 1 ≤ W u)
    (hedge : ∀ x y, T.Adj x y → δ y ≤ K * δ x)
    (hinside : ∀ x y, D.block x = D.block y → δ y ≤ W (D.block x) * δ x)
    (m : Λ → V) (hm : ∀ u, τ.degree u = 1 → D.block (m u) = u) :
    (∏ v : Nonroot a, r (D.childEnd v) * r (D.parentEnd v)) *
      (∏ l : Leaf τ a, r (m l) / δ (m l)) * (r (m a) / δ (m a)) ≤
      K ^ (Fintype.card V - 1) * (∏ u, W u) * (∏ u, R u ^ 2) / δ (m a) ^ 2 := by
  obtain ⟨h, hh⟩ := exists_isHeavyChoice (T := τ) (r := a)
  have hh' := hh.isChildChoice
  have ht := D.transport_xStar_denominators (h := h) hτ hT hK hδ hedge
  have heq : (∏ S' : D.xStar, 1 / δ S') = ∏ l : Leaf τ a, 1 / δ (D.start l) := by
    rw [← Finset.prod_subtype D.xStar (fun _ => Iff.rfl) (fun S => 1 / δ S),
      BlockTree.xStar, Finset.prod_image D.start_injective.injOn]
  rw [heq] at ht
  simp_rw [D.card_locPartFiber hτ] at ht
  have hc := D.compensate_all hτ hh' ha hr hδ hrδ hR hrR (m a) (hm a ha)
    (fun S hS => by
      have := hinside S (m a) (hS.trans (hm a ha).symm)
      simpa only [hS] using this)
  let Br := ∏ v : Nonroot a, r (D.childEnd v) * r (D.parentEnd v)
  let Q := ∏ S, (1 / δ S) ^ (attachmentFiber (h := h) hτ D.parentEnd S).card
  let RL := ∏ l : Leaf τ a, R l
  let WL := ∏ l : Leaf τ a, W l
  let C := K ^ (Fintype.card V - 1)
  have hBr0 : 0 ≤ Br := prod_nonneg fun v _ => mul_nonneg (hr _) (hr _)
  have hRL0 : 0 ≤ RL := prod_nonneg fun l _ => hR _
  have hWL0 : 0 ≤ WL := prod_nonneg fun l _ => zero_le_one.trans (hW _)
  have hC0 : 0 ≤ C := pow_nonneg (zero_le_one.trans hK) _
  have hroot0 : 0 ≤ r (m a) / δ (m a) := div_nonneg (hr _) (hδ _).le
  -- Keep just one marked ratio in each leaf block and move its denominator
  -- to the starting attachment of the lift.
  have hmarks : (∏ l : Leaf τ a, r (m l) / δ (m l)) ≤
      (WL * RL) * ∏ l : Leaf τ a, 1 / δ (D.start l) := by
    calc (∏ l : Leaf τ a, r (m l) / δ (m l)) ≤
        ∏ l : Leaf τ a, ((W l * R l) * (1 / δ (D.start l))) := by
          apply prod_le_prod₀ (fun l _ => div_nonneg (hr _) (hδ _).le)
          intro l _
          have hl : τ.degree l = 1 := mem_leaves.1 (mem_erase.1 l.property).2
          have hml := hm l hl
          have hdist := hinside (m l) (D.start l) (hml.trans (D.block_start l).symm)
          rw [hml] at hdist
          have hrm : r (m l) ≤ R l := by simpa only [hml] using hrR (m l)
          rw [mul_one_div, div_le_div_iff₀ (hδ _) (hδ _)]
          calc r (m l) * δ (D.start l) ≤ R l * (W l * δ (m l)) :=
              mul_le_mul hrm hdist (hδ _).le (hR _)
            _ = _ := by ring
    _ = _ := by simp only [prod_mul_distrib]; rfl
  -- Leaf blocks and the root are distinct, so each local comparison is paid once.
  have hcost : WL * W a ≤ ∏ u, W u := by
    have hsub : insert a ((leaves τ).erase a) ⊆ (univ : Finset Λ) := subset_univ _
    have hprod := Finset.prod_le_prod_of_subset_of_one_le₀ hsub (fun u _ => (zero_le_one.trans (hW u))) (fun u _ _ => hW u)
    rw [prod_insert (notMem_erase a _)] at hprod
    dsimp only [WL]
    rw [Finset.prod_coe_sort, mul_comm]
    exact hprod
  calc Br * (∏ l : Leaf τ a, r (m l) / δ (m l)) * (r (m a) / δ (m a))
      ≤ Br * ((WL * RL) * (C * Q)) * (r (m a) / δ (m a)) := by
        apply mul_le_mul_of_nonneg_right _ hroot0
        apply mul_le_mul_of_nonneg_left _ hBr0
        exact hmarks.trans (mul_le_mul_of_nonneg_left ht (mul_nonneg hWL0 hRL0))
    _ = (WL * C) * (Br * RL * Q * (r (m a) / δ (m a))) := by ring
    _ ≤ (WL * C) * (W a * (∏ u, R u ^ 2) / δ (m a) ^ 2) :=
      mul_le_mul_of_nonneg_left hc (mul_nonneg hWL0 hC0)
    _ = (WL * C * W a) * (∏ u, R u ^ 2) / δ (m a) ^ 2 := by ring
    _ ≤ _ := by
      rw [mul_assoc WL C, mul_comm C (W a), ← mul_assoc WL (W a), mul_comm (WL * W a) C]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcost hC0)
          (prod_nonneg fun u _ => sq_nonneg _)) (sq_nonneg _)

end MultipoleBKT.UpperBound.Quadratic

end
