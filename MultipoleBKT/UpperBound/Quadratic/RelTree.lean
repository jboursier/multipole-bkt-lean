/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Quadratic.PlusTree

/-!
# `𝒯_+^X ∈ 𝖳^X`

The paper: the paragraph before Definition 5.29: "From
every minimally 2-edge-connected block of the reduced skeleton we extract a spanning tree …
Adding the pendant trees together with the collection of bridges then produces a spanning tree of
the whole graph relative to `X`." This claim, used without proof in Corollary 5.34 (the sum over
`B(·, 𝒯_+^X)` is a sum over trees `T' ∈ 𝖳^X` containing `𝒯_+^X` itself), is proved here.

For a minimal skeleton `E` with `E ∪ ℰ^intra` connected and an admissible peeling `(Ts, Fs)` of its
bridge-blocks:

* `reachable_tree_of_inBlock`: `𝒯^{X_l} ∪ ℰ^intra` connects the bridge-block `l`;
* `natCard_tree_add_one`: `|𝒯^{X_l}| + 1 = |X_l|`;
* `connected_plusTree`: `𝒯_+^X ∪ ℰ^intra` is connected;
* `natCard_plusTree_add_one`: `|𝒯_+^X| + 1 = |β|` (for a surjective block map);
* `isRelTree_plusTree`: **`𝒯_+^X ∈ 𝖳^X`** for a subpartition `X` with `|X| ≥ 2`.
-/

@[expose] public section

open Finset SimpleGraph

namespace MultipoleBKT

namespace UpperBound

namespace Quadratic

open CoreForest Peeling

section Union

variable {V : Type*} [Fintype V]

/-- The number of edges of `(⨆ i, G i) ⊔ H` for pairwise disjoint `G i`, disjoint from `H`. -/
theorem natCard_edgeSet_iSup_sup {ι : Type*} [Fintype ι] {G : ι → SimpleGraph V}
    {H : SimpleGraph V} (hG : ∀ i j, i ≠ j → Disjoint (G i) (G j))
    (hGH : ∀ i, Disjoint (G i) H) :
    Nat.card ((⨆ i, G i) ⊔ H).edgeSet = ∑ i, Nat.card (G i).edgeSet + Nat.card H.edgeSet := by
  classical
  have hset : ((⨆ i, G i) ⊔ H).edgeFinset =
      (univ.biUnion fun i => (G i).edgeFinset) ∪ H.edgeFinset := by
    ext e
    simp only [mem_edgeFinset, edgeSet_sup, edgeSet_iSup, Set.mem_union, Set.mem_iUnion,
      Finset.mem_union, Finset.mem_biUnion, mem_univ, true_and]
  have hc : ∀ K : SimpleGraph V, Nat.card K.edgeSet = K.edgeFinset.card := fun K => by
    rw [edgeFinset_card, Nat.card_eq_fintype_card]
  have key : ((⨆ i, G i) ⊔ H).edgeFinset.card =
      ∑ i, (G i).edgeFinset.card + H.edgeFinset.card := by
    rw [hset, Finset.card_union_of_disjoint, Finset.card_biUnion]
    · intro i _ j _ hij
      exact disjoint_edgeFinset_of_disjoint (hG i j hij)
    · rw [Finset.disjoint_biUnion_left]
      exact fun i _ => disjoint_edgeFinset_of_disjoint (hGH i)
  simp only [hc]
  convert key using 2
  congr 1
  exact Subsingleton.elim _ _

end Union

section Tree

variable {V β : Type*} [Fintype V] [Fintype β] [DecidableEq β] {b : V → β}
  {E : SimpleGraph V} {r : V → ℝ} {d : Sym2 V → ℝ}
  {v₁ : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → V}
  {e₀ : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → Sym2 V}
  {Ts Fs : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → SimpleGraph V}
  (hE : E ≤ crossBlockGraph b) (hEE : IsMinimalSkeleton b E E)
  (hP : IsPlusPeeling b E (blockInnerEdges b E) r d v₁ e₀ Ts Fs)
include hE hEE hP

omit hE hEE in
/-- `𝒯^{X_l} ∪ ℰ^intra` connects the bridge-block `l` (Definition 4.43: deleting one edge from each
ear leaves a graph connected relative to the blocks). -/
theorem reachable_tree_of_inBlock (l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent)
    {x y : V} (hx : bridgeBlock b (coreEdges b E) x = l)
    (hy : bridgeBlock b (coreEdges b E) y = l) : (Ts l ⊔ sameBlockGraph b).Reachable x y := by
  classical
  by_cases h1 : (blockParts b E l).card = 1
  · obtain ⟨S, hS⟩ := Finset.card_eq_one.1 h1
    have hbx : b x ∈ blockParts b E l := mem_blockParts.2 ⟨x, hx, rfl⟩
    have hby : b y ∈ blockParts b E l := mem_blockParts.2 ⟨y, hy, rfl⟩
    rw [hS, mem_singleton] at hbx hby
    exact reachable_sup_sameBlockGraph_of_eq (hbx.trans hby.symm)
  · obtain ⟨w₁, e₀', Qs, hp, -, -, hT, -⟩ := (hP l).1 h1
    have hconn := hp.decomp.connected_keptGraph hp.isRemoval
    have hr := hconn.preconnected ⟨x, hx⟩ ⟨y, hy⟩
    refine reachable_comp_of_forall_adj (G' := Ts l ⊔ sameBlockGraph b) Subtype.val
      (fun u w huw => ?_) hr
    rcases huw with hk | hs
    · refine Adj.reachable (Or.inl ?_)
      rw [hT, map_adj]
      exact ⟨u, w, hk, rfl, rfl⟩
    · refine Adj.reachable (Or.inr ?_)
      obtain ⟨hne, hb⟩ := sameBlockGraph_adj.1 hs
      exact sameBlockGraph_adj.2 ⟨fun h => hne (Subtype.ext h), blockOn_eq_iff.1 hb⟩

omit hE hEE in
/-- `|𝒯^{X_l}| + 1 = |X_l|`. -/
theorem natCard_tree_add_one (l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent) :
    Nat.card (Ts l).edgeSet + 1 = (blockParts b E l).card := by
  classical
  by_cases h1 : (blockParts b E l).card = 1
  · rw [((hP l).2 h1).1, edgeSet_bot, h1]
    simp
  · obtain ⟨w₁, e₀', Qs, hp, -, -, hT, -⟩ := (hP l).1 h1
    rw [hT, natCard_edgeSet_map, hp.decomp.natCard_keptGraph hp.isRemoval, card_partsOn_eq]

/-- `𝒯_+^X ∪ ℰ^intra` is connected when `E ∪ ℰ^intra` is. -/
theorem connected_plusTree (hconn : (E ⊔ sameBlockGraph b).Connected) :
    (plusTree b E Ts ⊔ sameBlockGraph b).Connected := by
  have hEeq := eq_iSup_sup_relBridges hE hEE
  have : Nonempty V := hconn.nonempty
  refine ⟨fun x y => reachable_closed
    (P := fun z => (plusTree b E Ts ⊔ sameBlockGraph b).Reachable x z)
    (fun u w hu huw => hu.trans ?_) (hconn.preconnected x y) (Reachable.refl x)⟩
  rw [plusTree_eq hE]
  rcases huw with hEuw | hs
  · rw [hEeq, sup_adj, iSup_adj] at hEuw
    rcases hEuw with ⟨l, hl⟩ | hb
    · rw [← (tree_sup_removed hE hEE hP l).1, sup_adj] at hl
      rcases hl with hT | hF
      · exact Adj.reachable (Or.inl (Or.inl ((iSup_adj).2 ⟨l, hT⟩)))
      · have hFl : (blockInnerEdges b E l).Adj u w := by
          rw [← (tree_sup_removed hE hEE hP l).1]
          exact Or.inr hF
        obtain ⟨hu', hw'⟩ := blockInnerEdges_adj_inBlock hFl
        refine (reachable_tree_of_inBlock hP l hu' hw').mono (sup_le_sup_right ?_ _)
        exact (le_iSup Ts l).trans le_sup_left
    · exact Adj.reachable (Or.inl (Or.inr hb))
  · exact Adj.reachable (Or.inr hs)

/-- `|𝒯_+^X| + 1 = |β|` for a surjective block map. -/
theorem natCard_plusTree_add_one (hconn : (E ⊔ sameBlockGraph b).Connected)
    (hb : Function.Surjective b) : Nat.card (plusTree b E Ts).edgeSet + 1 = Fintype.card β := by
  classical
  have hTle : ∀ l, Ts l ≤ blockInnerEdges b E l := fun l =>
    (tree_sup_removed hE hEE hP l).1 ▸ le_sup_left
  rw [plusTree_eq hE, natCard_edgeSet_iSup_sup
    (fun l l' h => (disjoint_blockInnerEdges h).mono (hTle l) (hTle l'))
    (fun l => (disjoint_blockInnerEdges_relBridges hE l).mono_left (hTle l))]
  have hbr := natCard_relBridges_add_one hE hconn
  obtain ⟨eqv, -⟩ := exists_componentEquiv (bridgelessGraph_eq hE)
  rw [Nat.card_congr eqv,
    Nat.card_eq_fintype_card (α := (bridgelessGraph b (coreEdges b E)).ConnectedComponent)] at hbr
  -- the blocks partition `β`
  have hpart : ∑ l, (blockParts b E l).card = Fintype.card β := by
    have hcov : (univ : Finset β) = univ.biUnion fun l => blockParts b E l := by
      ext S
      simp only [mem_univ, mem_biUnion, true_and, true_iff]
      obtain ⟨v, hv⟩ := hb S
      exact ⟨_, mem_blockParts.2 ⟨v, rfl, hv⟩⟩
    rw [← Finset.card_univ, hcov, Finset.card_biUnion]
    intro l _ l' _ hll'
    rw [Function.onFun, Finset.disjoint_left]
    intro S hS hS'
    obtain ⟨v, hv, rfl⟩ := mem_blockParts.1 hS
    obtain ⟨w, hw, hwv⟩ := mem_blockParts.1 hS'
    exact hll' (hv.symm.trans ((bridgeBlock_eq_of_eq hwv).symm.trans hw))
  rw [← hpart, ← Finset.sum_congr rfl fun l _ => natCard_tree_add_one hP l,
    Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, ← hbr]
  ring

end Tree

section Subpartition

variable {X : Finset (Finset ℕ)} (hX : IsSubpartition X)

/-- **`𝒯_+^X ∈ 𝖳^X`** (Section 5.6): for a minimal skeleton `E ⊆ ℰ^inter(X)` with `E ∪ ℰ^intra`
connected, `|X| ≥ 2`, and an admissible peeling of its bridge-blocks, `𝒯_+^X(·, E)` is a tree
relative to `X`. -/
theorem isRelTree_plusTree {E : SimpleGraph (X.biUnion id)} {r : X.biUnion id → ℝ}
    {d : Sym2 (X.biUnion id) → ℝ}
    {v₁ : (bridgelessGraph (blockOf hX) (coreEdges (blockOf hX) E)).ConnectedComponent →
      X.biUnion id}
    {e₀ : (bridgelessGraph (blockOf hX) (coreEdges (blockOf hX) E)).ConnectedComponent →
      Sym2 (X.biUnion id)}
    {Ts Fs : (bridgelessGraph (blockOf hX) (coreEdges (blockOf hX) E)).ConnectedComponent →
      SimpleGraph (X.biUnion id)}
    (hE : E ≤ crossBlockGraph (blockOf hX)) (hEE : IsMinimalSkeleton (blockOf hX) E E)
    (hP : IsPlusPeeling (blockOf hX) E (blockInnerEdges (blockOf hX) E) r d v₁ e₀ Ts Fs)
    (hconn : (E ⊔ sameBlockGraph (blockOf hX)).Connected) (hX2 : 2 ≤ X.card) :
    IsRelTree X (plusTree (blockOf hX) E Ts) := by
  have hTE : plusTree (blockOf hX) E Ts ≤ E := by
    rw [plusTree_eq hE]
    refine sup_le (iSup_le fun l => ?_) relBridges_le
    exact ((tree_sup_removed hE hEE hP l).1 ▸ le_sup_left).trans (blockInnerEdges_le l)
  have hT : plusTree (blockOf hX) E Ts ≤ interEdges X := by
    rw [interEdges_eq hX]
    exact hTE.trans hE
  have hconnT := connected_plusTree hE hEE hP hconn
  rw [← intraEdges_eq hX, connected_sup_intraEdges_iff hX] at hconnT
  have hcard := natCard_plusTree_add_one hE hEE hP hconn (blockOf_surjective hX)
  rw [Fintype.card_coe] at hcard
  have hQle : Nat.card (quotientGraph X (plusTree (blockOf hX) E Ts)).edgeSet ≤
      Nat.card (plusTree (blockOf hX) E Ts).edgeSet := by
    rw [quotientGraph_eq hX]
    rw [interEdges_eq hX] at hT
    exact natCard_blockQuotient_edgeSet_le _ hT
  have hQge := hconnT.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at hQge
  have htree : (quotientGraph X (plusTree (blockOf hX) E Ts)).IsTree := by
    rw [isTree_iff_connected_and_card, Nat.card_eq_fintype_card (α := X), Fintype.card_coe]
    exact ⟨hconnT, by omega⟩
  have h₀ : IsRelTree₀ X (plusTree (blockOf hX) E Ts) :=
    (isRelTree₀_iff_card hX).mpr ⟨hT, htree, hcard⟩
  exact h₀.resolve_right fun h => by omega

end Subpartition

end Quadratic

end UpperBound

end MultipoleBKT

end
