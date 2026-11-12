/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Quadratic.TreeBound
public import MultipoleBKT.UpperBound.Quadratic.Structure
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Bad-distance comparisons along walks

The paper: Corollary 5.34. This module supplies comparisons along walks and the removal
of factors in `[0, 1]`. The lifted bridge and mark estimate used in the summed
quadratic proof is `RouteLift.bridges_marks_le_parts`.
-/

@[expose] public section

open Finset SimpleGraph

namespace MultipoleBKT

namespace UpperBound

namespace Quadratic

open CoreForest Peeling

/-! ### Comparisons along walks -/

section Walk

variable {V : Type*} {G : SimpleGraph V} {δ : V → ℝ} {K : ℝ}

/-- If `δ_w ≤ K δ_u` along every edge `uw`, then `δ_y ≤ K^{|p|} δ_x` along a walk `p` from `x` to
`y` (the chain estimates (5.13), (5.14)). -/
theorem le_pow_length_mul (hK : 0 ≤ K) (hG : ∀ u w, G.Adj u w → δ w ≤ K * δ u)
    (hδ : ∀ v, 0 ≤ δ v) : ∀ {x y : V} (p : G.Walk x y), δ y ≤ K ^ p.length * δ x
  | _, _, .nil => by simp
  | _, _, .cons h q => by
      rw [Walk.length_cons, pow_succ]
      calc _ ≤ K ^ q.length * δ _ := le_pow_length_mul hK hG hδ q
        _ ≤ K ^ q.length * (K * δ _) := mul_le_mul_of_nonneg_left (hG _ _ h) (pow_nonneg hK _)
        _ = _ := by ring

/-- The chain estimate inside a finite set: if every vertex reachable from `x` lies in `S`, then
`δ_y ≤ K^{|S|} δ_x` for every `y` reachable from `x` (`K ≥ 1`). -/
theorem le_pow_card_mul [DecidableEq V] (hK : 1 ≤ K) (hG : ∀ u w, G.Adj u w → δ w ≤ K * δ u)
    (hδ : ∀ v, 0 ≤ δ v) {S : Finset V} {x y : V} (h : G.Reachable x y)
    (hS : ∀ v, G.Reachable x v → v ∈ S) : δ y ≤ K ^ S.card * δ x := by
  obtain ⟨w⟩ := h
  have hq : w.bypass.IsPath := w.bypass_isPath
  have hlen : w.bypass.length + 1 ≤ S.card := by
    rw [← Walk.length_support, ← List.toFinset_card_of_nodup hq.support_nodup]
    exact Finset.card_le_card fun v hv =>
      hS v ⟨w.bypass.takeUntil v (List.mem_toFinset.1 hv)⟩
  calc δ y ≤ K ^ w.bypass.length * δ x := le_pow_length_mul (by linarith) hG hδ _
    _ ≤ K ^ S.card * δ x :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK (by omega)) (hδ x)

end Walk

/-- Dropping factors in `[0, 1]`. -/
theorem prod_le_prod_of_subset_of_le_one {ι : Type*} [DecidableEq ι] {s t : Finset ι}
    {f : ι → ℝ} (hts : t ⊆ s) (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  rw [← Finset.prod_sdiff hts]
  calc (∏ i ∈ s \ t, f i) * ∏ i ∈ t, f i ≤ 1 * ∏ i ∈ t, f i :=
        mul_le_mul_of_nonneg_right
          (Finset.prod_le_one₀ (fun i hi => h0 i (mem_sdiff.1 hi).1)
            fun i hi => h1 i (mem_sdiff.1 hi).1)
          (Finset.prod_nonneg fun i hi => h0 i (hts hi))
    _ = _ := one_mul _


end Quadratic

end UpperBound

end MultipoleBKT

end
