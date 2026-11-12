/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The product over the optional edges of a Penrose fiber

The interval sum in (4.86) and (4.87).
A graph between `L` and `U` is uniquely `L` together with a subset of
`E(U) ∖ E(L)`. Factor out the edges of `L` and expand the remaining product.
-/

@[expose] public section

namespace MultipoleBKT.RouteCounts

open Finset SimpleGraph

variable {V R : Type*} [Fintype V] [CommSemiring R]

open scoped Classical in
/-- Reconstructing a subset of a graph's edges introduces no loops. -/
theorem edgeFinset_from_subset (G : SimpleGraph V) (s : Finset (Sym2 V))
    (hs : s ⊆ G.edgeFinset) : (fromEdgeSet (s : Set (Sym2 V))).edgeFinset = s := by
  ext e
  simp only [mem_edgeFinset, edgeSet_fromEdgeSet, Set.mem_sdiff, mem_coe]
  exact ⟨And.left, fun he => ⟨he, G.not_isDiag_of_mem_edgeSet (mem_edgeFinset.mp (hs he))⟩⟩

open scoped Classical in
/-- The Penrose interval product, with arbitrary edge weights. -/
theorem sum_graph_interval_prod [Fintype (SimpleGraph V)] (L U : SimpleGraph V)
    (hLU : L ≤ U) (c : Sym2 V → R) :
    ∑ H ∈ (univ : Finset (SimpleGraph V)).filter (fun H => L ≤ H ∧ H ≤ U),
        ∏ e ∈ H.edgeFinset, c e =
      (∏ e ∈ L.edgeFinset, c e) * ∏ e ∈ U.edgeFinset \ L.edgeFinset, (1 + c e) := by
  let S := U.edgeFinset \ L.edgeFinset
  have hsub := edgeFinset_mono hLU
  have hbuild : ∀ s ∈ S.powerset,
      (fromEdgeSet ((L.edgeFinset ∪ s : Finset (Sym2 V)) : Set (Sym2 V))).edgeFinset =
        L.edgeFinset ∪ s := by
    intro s hs
    exact edgeFinset_from_subset U _ (union_subset hsub
      ((mem_powerset.mp hs).trans sdiff_subset))
  have hsum : (∑ H ∈ (univ : Finset (SimpleGraph V)).filter (fun H => L ≤ H ∧ H ≤ U),
        ∏ e ∈ H.edgeFinset, c e) =
      ∑ s ∈ S.powerset, (∏ e ∈ L.edgeFinset, c e) * ∏ e ∈ s, c e := by
    refine sum_bij (fun H _ => H.edgeFinset \ L.edgeFinset) ?_ ?_ ?_ ?_
    · intro H hH
      rw [mem_filter] at hH
      exact mem_powerset.mpr (sdiff_subset_sdiff (edgeFinset_mono hH.2.2) subset_rfl)
    · intro H₁ h₁ H₂ h₂ heq
      apply edgeFinset_inj.mp
      have hl₁ := edgeFinset_mono (mem_filter.mp h₁).2.1
      have hl₂ := edgeFinset_mono (mem_filter.mp h₂).2.1
      rw [← union_sdiff_of_subset hl₁, ← union_sdiff_of_subset hl₂, heq]
    · intro s hs
      refine ⟨fromEdgeSet ((L.edgeFinset ∪ s : Finset (Sym2 V)) : Set (Sym2 V)), ?_, ?_⟩
      · rw [mem_filter]
        refine ⟨mem_univ _, ?_, ?_⟩
        · rw [← edgeFinset_subset_edgeFinset, hbuild s hs]
          exact subset_union_left
        · rw [← edgeFinset_subset_edgeFinset, hbuild s hs]
          exact union_subset hsub ((mem_powerset.mp hs).trans sdiff_subset)
      · ext e
        simp only [mem_sdiff, mem_edgeFinset, edgeSet_fromEdgeSet, Set.mem_sdiff,
          mem_coe, mem_union]
        constructor
        · rintro ⟨⟨he | he, _⟩, hn⟩
          · exact False.elim (hn he)
          · exact he
        · intro he
          have heU := mem_edgeFinset.mp ((mem_sdiff.mp (mem_powerset.mp hs he)).1)
          exact ⟨⟨Or.inr he, U.not_isDiag_of_mem_edgeSet heU⟩,
            fun hm => (mem_sdiff.mp (mem_powerset.mp hs he)).2 (mem_edgeFinset.mpr hm)⟩
    · intro H hH
      have hl := edgeFinset_mono (mem_filter.mp hH).2.1
      rw [← prod_union disjoint_sdiff_self_right, union_sdiff_of_subset hl]
  rw [hsum, ← mul_sum, ← prod_one_add]

end MultipoleBKT.RouteCounts

end
