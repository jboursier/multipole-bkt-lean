/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Frozen.Ursell
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Subgraph sums supporting the Ursell chromatic identity

See equation (4.150) of the paper.

Reachability and edge-count helpers support the incidence-tree construction.
Spanning subgraphs correspond to edge subsets, whose alternating sum vanishes
unless the graph has no edges. This cancellation supplies the inclusion-exclusion
proof of the chromatic polynomial. Filtering its subgraph sum by connectedness
identifies the linear coefficient with the Ursell function.
-/

@[expose] public section

namespace MultipoleBKT

open Finset SimpleGraph

variable {V : Type*}

section Graphs

/-- If every adjacency of `G` is a reachability in `G'`, every reachability in `G` is one in
`G'`. -/
theorem reachable_of_forall_adj_reachable {G G' : SimpleGraph V}
    (h : ∀ u v, G.Adj u v → G'.Reachable u v) {u v : V} (huv : G.Reachable u v) :
    G'.Reachable u v := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => exact Reachable.refl _
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

/-- If every adjacency of a connected graph `G` is a reachability in `G'`, then `G'` is
connected. -/
theorem connected_of_forall_adj_reachable {G G' : SimpleGraph V} (hG : G.Connected)
    (h : ∀ u v, G.Adj u v → G'.Reachable u v) : G'.Connected where
  preconnected u v := reachable_of_forall_adj_reachable h (hG u v)
  nonempty := hG.nonempty

/-- Adjacency in a finite supremum of graphs. -/
theorem finsetSup_adj {ι : Type*} (s : Finset ι) (K : ι → SimpleGraph V) {x y : V} :
    (s.sup K).Adj x y ↔ ∃ i ∈ s, (K i).Adj x y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s _ ih => simp [sup_adj, ih]

/-- Every edge of a finite supremum of graphs is an edge of one of them. -/
theorem exists_mem_edgeSet_of_mem_finsetSup {ι : Type*} (s : Finset ι) (K : ι → SimpleGraph V)
    {e : Sym2 V} (he : e ∈ (s.sup K).edgeSet) : ∃ i ∈ s, e ∈ (K i).edgeSet := by
  induction e using Sym2.ind with
  | h x y => exact (finsetSup_adj s K).mp he

end Graphs

variable [Fintype V]

open scoped Classical in
/-- Unfolding of the Ursell function. -/
theorem ursell_eq_sum (G : SimpleGraph V) :
    ursell G = ∑ H ∈ (univ : Finset (SimpleGraph V)).filter (fun H => H ≤ G ∧ H.Connected),
      (-1) ^ H.edgeFinset.card := rfl

omit [Fintype V] in
/-- The number of edges, independently of the `Fintype` instance on the edge set. -/
theorem card_edgeFinset_eq_ncard (H : SimpleGraph V) [Fintype H.edgeSet] :
    H.edgeFinset.card = H.edgeSet.ncard :=
  (Set.ncard_eq_toFinset_card' _).symm

section Alternating

open scoped Classical

/-- Spanning subgraphs of `K` correspond to subsets of its edge set. -/
theorem sum_filter_le_eq_sum_powerset {M : Type*} [AddCommMonoid M] (K : SimpleGraph V)
    (f : SimpleGraph V → M) :
    ∑ H ∈ (univ : Finset (SimpleGraph V)).filter (· ≤ K), f H =
      ∑ F ∈ K.edgeFinset.powerset, f (fromEdgeSet (F : Set (Sym2 V))) := by
  have hF : ∀ F ∈ K.edgeFinset.powerset, (fromEdgeSet (F : Set (Sym2 V))).edgeFinset = F := by
    intro F hF
    rw [mem_powerset] at hF
    ext e
    simp only [mem_edgeFinset, edgeSet_fromEdgeSet, Set.mem_sdiff, mem_coe,
      and_iff_left_iff_imp]
    intro he
    exact not_isDiag_of_mem_edgeSet _ (by simpa using hF he)
  refine Finset.sum_nbij' (fun H => H.edgeFinset) (fun F => fromEdgeSet (F : Set (Sym2 V)))
    ?_ ?_ ?_ ?_ ?_
  · intro H hH
    simp only [mem_filter, mem_univ, true_and] at hH
    simpa using edgeFinset_mono hH
  · intro F hF'
    simp only [mem_filter, mem_univ, true_and]
    rw [← edgeFinset_subset_edgeFinset, hF F hF']
    exact mem_powerset.mp hF'
  · intro H _
    simp
  · intro F hF'
    convert hF F hF'
  · intro H _
    simp

/-- The alternating sum over all spanning subgraphs of `K` is `1` if `K` has no edge and `0`
otherwise. -/
theorem sum_neg_one_pow_edges_le (K : SimpleGraph V) :
    ∑ H ∈ (univ : Finset (SimpleGraph V)).filter (· ≤ K), ((-1 : ℤ) ^ H.edgeFinset.card) =
      if K = ⊥ then 1 else 0 := by
  rw [sum_filter_le_eq_sum_powerset]
  rw [Finset.sum_congr rfl fun F hF => ?_, Finset.sum_powerset_neg_one_pow_card]
  · simp
  · rw [mem_powerset] at hF
    congr 2
    ext e
    simp only [mem_edgeFinset, edgeSet_fromEdgeSet, Set.mem_sdiff, mem_coe,
      and_iff_left_iff_imp]
    intro he
    exact not_isDiag_of_mem_edgeSet _ (by simpa using hF he)

end Alternating

section Product

open scoped Classical

/-- Rewriting a sum over the spanning subgraphs of `X` satisfying `Q`. -/
theorem sum_filter_le_and {M : Type*} [AddCommMonoid M] (X : SimpleGraph V)
    (Q : SimpleGraph V → Prop) [DecidablePred Q] [DecidablePred fun H => H ≤ X ∧ Q H]
    (f : SimpleGraph V → M) :
    ∑ H ∈ (univ : Finset (SimpleGraph V)).filter (fun H => H ≤ X ∧ Q H), f H =
      ∑ H ∈ (univ : Finset (SimpleGraph V)).filter (· ≤ X), if Q H then f H else 0 := by
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun H _ => ?_
  by_cases h1 : H ≤ X <;> by_cases h2 : Q H <;> simp [h1, h2]

end Product

end MultipoleBKT

end
