/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.Skeleton

/-!
# The quadratic omitted-long-edge gain

See Step 3 of
the proof of Lemma A.7. A surplus edge contributes its quadratic
bound directly. Inside an odd skeleton, open a longest edge and retain the
minimum of the cutoff gain and the one maximal-distance tail of the kept tree.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset SimpleGraph Peeling Limits

variable {V κ : Type*} [Fintype V] [DecidableEq V] [Fintype κ] [DecidableEq κ]
variable {b : V → κ} {E : SimpleGraph V} {r : V → ℝ} {d c : Sym2 V → ℝ}
variable {v : V} {e₀ : Sym2 V} {Qs : List (Ear V × (V × V))}

open scoped Classical in
/-- The discarded weights retain one global tail on the kept tree. -/
theorem deleted_weights_single_tail (hp : IsPeelingOn b E r d v e₀ Qs)
    (hr : ∀ i, 0 ≤ r i) (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
    (hpos : ∀ e ∈ (keptGraph E Qs).edgeSet, 0 < d e) :
    ∏ e ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v) e₀ e ≤
      globalTail (r v) d (keptGraph E Qs).edgeFinset := by
  apply (le_fold_min _).2
  refine ⟨hp.prod_peelWeight_le_one hr hc hc1, fun e he => ?_⟩
  refine le_min (hp.prod_peelWeight_le_one hr hc hc1) ?_
  exact (le_div_iff₀ (pow_pos (hpos e (mem_edgeFinset.1 he)) 2)).2
    (hp.prod_peelWeight_mul_sq_le hr hd hc hc1 (mem_edgeFinset.1 he))

open scoped Classical in
/-- Opening the longest original edge gives a quadratic gain at any smaller
positive distance threshold. The exponent remains exactly two. -/
theorem deleted_weights_quadratic (hp : IsPeelingOn b E r d v e₀ Qs)
    (hr : ∀ i, 0 ≤ r i) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
    {em : Sym2 V} (hem : em ∈ E.edgeSet) {H : ℝ} (hH : 0 < H)
    (hRH : r v ≤ H) (hm : H ≤ d em) :
    ∏ e ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v) e₀ e ≤ r v ^ 2 / H ^ 2 := by
  have hHd : H ≤ d e₀ := hm.trans (hp.le_longest em hem)
  have hd₀ : 0 < d e₀ := hH.trans_le hHd
  have hRd : r v ≤ d e₀ := hRH.trans hHd
  have he₀ : e₀ ∈ (removedGraph Qs).edgeFinset := by
    rw [mem_edgeFinset, removedGraph, edgeSet_fromEdgeSet, Set.mem_sdiff]
    exact ⟨hp.longest_mem_removedEdges hRd, not_isDiag_of_mem_edgeSet _ hp.longest_mem⟩
  have hg : peelWeight r d c (r v) e₀ e₀ ≤ r v ^ 2 / d e₀ ^ 2 := by
    rw [peelWeight, ite_eq_right (not_lt.2 ((radMax_le_of_le hp.le_radius e₀).trans hRd)),
      ite_eq_left ⟨rfl, hRd⟩]
    exact mul_le_of_le_one_left (div_nonneg (sq_nonneg _) (sq_nonneg _)) (hc1 _)
  rw [← mul_prod_erase _ _ he₀]
  calc peelWeight r d c (r v) e₀ e₀ *
        (∏ e ∈ (removedGraph Qs).edgeFinset.erase e₀, peelWeight r d c (r v) e₀ e) ≤
      peelWeight r d c (r v) e₀ e₀ :=
        mul_le_of_le_one_right (peelWeight_nonneg hc _ _) (prod_le_one₀
          (fun e _ => peelWeight_nonneg hc _ _) (fun e _ => peelWeight_le_one hr hc1 (hr v) _ _))
    _ ≤ r v ^ 2 / d e₀ ^ 2 := hg
    _ ≤ r v ^ 2 / H ^ 2 := div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hH 2)
      (pow_le_pow_left₀ hH.le hHd 2)

open scoped Classical in
/-- The literal minimum retained for an omitted long odd skeleton edge.
The maximal-distance tail is not distributed among the tree edges. -/
theorem long_odd_skeleton_product (hp : IsPeelingOn b E r d v e₀ Qs)
    (hr : ∀ i, 0 ≤ r i) (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
    (ρ : κ → ℝ) (hrρ : ∀ i, r i ≤ ρ (b i))
    (hpos : ∀ e ∈ (keptGraph E Qs).edgeSet, 0 < d e)
    {em : Sym2 V} (hem : em ∈ E.edgeSet) {H : ℝ} (hH : 0 < H)
    (hRH : r v ≤ H) (hm : H ≤ d em) :
    ∏ e ∈ E.edgeFinset, absWeight r d c e ≤
      (∏ S ∈ univ.erase (b v), ρ S ^ 2) *
        (∏ e ∈ (keptGraph E Qs).edgeFinset, keptWeight d c e) *
          min (r v ^ 2 / H ^ 2) (globalTail (r v) d (keptGraph E Qs).edgeFinset) := by
  have hg := le_min (deleted_weights_quadratic hp hr hc hc1 hem hH hRH hm)
    (deleted_weights_single_tail hp hr hd hc hc1 hpos)
  exact (hp.prod_absWeight_le hr hd hc ρ hrρ).trans
    (mul_le_mul_of_nonneg_left hg (mul_nonneg (prod_nonneg fun S _ => sq_nonneg _)
      (prod_nonneg fun e _ => keptWeight_nonneg hc e)))

/-- Combining all odd components keeps both the quadratic long-edge gain and
one global maximal-distance tail. The gain is not spread over separate edges. -/
theorem long_odd_forest_tail {α ε : Type*} [DecidableEq α] [DecidableEq ε]
    (C : Finset α) (T : α → Finset ε) (d : ε → ℝ) (r : α → ℝ) {R H : ℝ}
    (hr : ∀ l ∈ C, 0 ≤ r l) (hR : ∀ l ∈ C, r l ≤ R)
    {l₀ : α} (hl₀ : l₀ ∈ C) :
    min (r l₀ ^ 2 / H ^ 2) (globalTail (r l₀) d (T l₀)) *
        (∏ l ∈ C.erase l₀, globalTail (r l) d (T l)) ≤
      min (R ^ 2 / H ^ 2) (globalTail R d (C.biUnion T)) := by
  have hp0 : 0 ≤ ∏ l ∈ C.erase l₀, globalTail (r l) d (T l) :=
    prod_nonneg fun l _ => globalTail_nonneg _ _ _
  have hp1 : ∏ l ∈ C.erase l₀, globalTail (r l) d (T l) ≤ 1 :=
    prod_le_one₀ (fun l _ => globalTail_nonneg _ _ _) (fun l _ => globalTail_le_one _ _ _)
  refine le_min ?_ ?_
  · calc _ ≤ (r l₀ ^ 2 / H ^ 2) * ∏ l ∈ C.erase l₀, globalTail (r l) d (T l) :=
           mul_le_mul_of_nonneg_right (min_le_left _ _) hp0
         _ ≤ r l₀ ^ 2 / H ^ 2 := mul_le_of_le_one_right (div_nonneg (sq_nonneg _) (sq_nonneg _)) hp1
         _ ≤ R ^ 2 / H ^ 2 := div_le_div_of_nonneg_right
           (pow_le_pow_left₀ (hr l₀ hl₀) (hR l₀ hl₀) 2) (sq_nonneg _)
  · calc _ ≤ globalTail (r l₀) d (T l₀) * ∏ l ∈ C.erase l₀, globalTail (r l) d (T l) :=
           mul_le_mul_of_nonneg_right (min_le_right _ _) hp0
         _ = ∏ l ∈ C, globalTail (r l) d (T l) := mul_prod_erase C (fun l => globalTail (r l) d (T l)) hl₀
         _ ≤ _ := prod_globalTail_le_biUnion C r R d T hr hR

/-- On a nonempty odd tree the retained minimum is exactly the displayed
minimum involving its longest edge, including the quadratic cutoff exponent. -/
theorem quadratic_tail_eq_of_max {ε : Type*} {R H : ℝ} (hR : 0 ≤ R) (hH : 0 < H)
    (hRH : R ≤ H) (d : ε → ℝ) {T : Finset ε} {em : ε} (hem : em ∈ T)
    (hd : ∀ e ∈ T, 0 < d e) (hmax : ∀ e ∈ T, d e ≤ d em) :
    min (R ^ 2 / H ^ 2) (globalTail R d T) = min (R ^ 2 / H ^ 2) (R ^ 2 / d em ^ 2) := by
  have hq : R ^ 2 / H ^ 2 ≤ 1 := (div_le_one (pow_pos hH 2)).2 (pow_le_pow_left₀ hR hRH 2)
  rw [globalTail_eq_of_max hem hd hmax, ← min_assoc, min_eq_left hq]

section Surplus

variable {ε : Type*} [DecidableEq ε]

/-- Internal product estimate for a surplus edge. Removing the mark does not
remove any edge of the retained skeleton or tree. -/
theorem internal_surplus_product (S K : Finset ε) (hKS : K ⊆ S) (a : ε → ℝ)
    (ha0 : ∀ e ∈ S, 0 ≤ a e) (ha1 : ∀ e ∈ S, a e ≤ 1)
    {em : ε} (hem : em ∈ S \ K) {q : ℝ} (hm : a em ≤ q) :
    ∏ e ∈ S, a e ≤ q * ∏ e ∈ K, a e := by
  have hKe : K ⊆ S.erase em := fun e he => mem_erase.2
    ⟨fun heq => (mem_sdiff.1 hem).2 (heq ▸ he), hKS he⟩
  have hrest : ∏ e ∈ S.erase em, a e ≤ ∏ e ∈ K, a e := by
    rw [← prod_sdiff hKe]
    exact mul_le_of_le_one_left (prod_nonneg fun e he => ha0 e (hKS he))
      (prod_le_one₀ (fun e he => ha0 e (mem_of_mem_erase (mem_sdiff.1 he).1))
        (fun e he => ha1 e (mem_of_mem_erase (mem_sdiff.1 he).1)))
  rw [← mul_prod_erase _ _ (mem_sdiff.1 hem).1]
  exact mul_le_mul hm hrest (prod_nonneg fun e he => ha0 e (mem_of_mem_erase he))
    ((ha0 em (mem_sdiff.1 hem).1).trans hm)

end Surplus

end MultipoleBKT.ExpansionK.RouteCases

end
