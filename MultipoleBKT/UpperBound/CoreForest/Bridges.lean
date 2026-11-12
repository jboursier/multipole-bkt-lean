/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Cluster.Relative

/-!
# Bridges, bridge-blocks and the bridge-tree relative to a partition

The paper: Definitions 5.25 (3)–(4) and 5.26 (3)–(4), and the decomposition used
in the proof of Corollary 5.34 ("delete all bridges of the multigraph quotient").
The tree property of the bridge-tree of the full quotient, used there without
proof, is proved here.

The vertices carry a block map `b : V → β` (for a subpartition `X`: `V = V_X`, `β = X`,
`b = [·]^X`), `E` is an edge set between distinct blocks (`E ≤ crossBlockGraph b`) and
`G = E ∪ ℰ^intra` is `E ⊔ sameBlockGraph b`. A bridge of the multigraph quotient `G/X` is exactly
an edge of `E` that is a bridge of `G`.

* `relBridges b E`: the bridges `ℰ_br`, the edges of `E` that are bridges of `G`;
* `bridgelessGraph b E`: the non-bridge edges of `E` together with the same-block edges;
* `bridgeBlock b E v`: the bridge-block of `v`, its connected component in `bridgelessGraph b E`
  (every block of `b` lies in one bridge-block; a single block without inner edges is a
  bridge-block, as the paper allows);
* `bridgeTree b E`: the quotient `(V, ℰ_br)/Y` of the bridges by the bridge-blocks `Y`.

Main results (all for `E ≤ crossBlockGraph b`):

* `relBridges_adj_iff`: an edge of `E` is a bridge iff it joins two distinct bridge-blocks; the
  other edges of `E` lie inside bridge-blocks (`bridgeBlock_eq_of_adj_of_not_relBridges`), so
  `E = (⋃ E(B)) ⊔ ℰ_br` (Definition 5.26 (4));
* `reachable_deleteEdges_of_bridgeBlock_eq`: every bridge-block is 2-edge-connected: deleting
  one inner edge of `E`, its vertices stay connected inside it;
* `bridgeBlock_eq_of_reachable_of_forall_not_isBridge`: maximality: the vertices of any subgraph
  of `G` in which no edge of `E` is a bridge lie in one bridge-block;
* `hasUniqueReps_relBridges`: two bridge-blocks are joined by at most one bridge;
* `bridgeTree_isAcyclic`, and `bridgeTree_isTree` when `G` is connected (`E ∈ 𝖤^X`): the
  bridge-tree is a tree (`ℰ_br ∈ 𝖳_0^Y`, Definition 5.26 (4)).
-/

@[expose] public section

namespace MultipoleBKT

namespace CoreForest

open Finset SimpleGraph

/-- **Lifting walks of a quotient.** Let `c : V → γ` have fibres connected in `H`. A walk of the
quotient of `K` by `c` lifts to a walk in `H ⊔ K` between any two vertices of its end fibres. -/
theorem reachable_of_reachable_blockQuotient' {V γ : Type*} {c : V → γ} {H K : SimpleGraph V}
    (hH : ∀ u v, c u = c v → H.Reachable u v) {C D : γ}
    (hCD : (blockQuotient c K).Reachable C D) {u v : V} (hu : c u = C) (hv : c v = D) :
    (H ⊔ K).Reachable u v := by
  obtain ⟨p⟩ := hCD
  induction p generalizing u with
  | nil => exact (hH u v (hu.trans hv.symm)).mono le_sup_left
  | cons hadj _ ih =>
    obtain ⟨-, a, d, ha, hd, had⟩ := blockQuotient_adj.mp hadj
    exact ((hH u a (hu.trans ha.symm)).mono le_sup_left).trans
      ((Adj.reachable (Or.inr had : (H ⊔ K).Adj a d)).trans (ih hd hv))

section Bridges

variable {V β : Type*} (b : V → β) (E : SimpleGraph V)

/-- The bridges `ℰ_br` of `E` relative to the blocks of `b`: the edges of `E` that are bridges of
`E ∪ ℰ^intra` (equivalently, bridges of the multigraph quotient by the blocks). -/
def relBridges : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | e ∈ E.edgeSet ∧ (E ⊔ sameBlockGraph b).IsBridge e}

/-- The edges of `E` that are not bridges, together with the same-block edges. -/
def bridgelessGraph : SimpleGraph V := (E \ relBridges b E) ⊔ sameBlockGraph b

/-- The bridge-block of a vertex: its connected component after deleting all bridges (Definitions
5.25 (3), 5.26 (3)). -/
def bridgeBlock (v : V) : (bridgelessGraph b E).ConnectedComponent :=
  (bridgelessGraph b E).connectedComponentMk v

/-- The bridge-tree `(V, ℰ_br)/Y`: the quotient of the bridges by the bridge-blocks (Definitions
5.25 (4), 5.26 (4)). -/
def bridgeTree : SimpleGraph (bridgelessGraph b E).ConnectedComponent :=
  blockQuotient (bridgeBlock b E) (relBridges b E)

variable {b E}

theorem relBridges_adj {u v : V} :
    (relBridges b E).Adj u v ↔ E.Adj u v ∧ (E ⊔ sameBlockGraph b).IsBridge s(u, v) := by
  rw [relBridges, fromEdgeSet_adj, Set.mem_ofPred_eq, mem_edgeSet]
  exact ⟨fun h => h.1, fun h => ⟨h, h.1.ne⟩⟩

theorem relBridges_le : relBridges b E ≤ E := fun _ _ h => (relBridges_adj.1 h).1

theorem bridgelessGraph_adj {u v : V} :
    (bridgelessGraph b E).Adj u v ↔
      (E.Adj u v ∧ ¬ (relBridges b E).Adj u v) ∨ (sameBlockGraph b).Adj u v := by
  rw [bridgelessGraph, sup_adj, sdiff_adj]

theorem bridgeBlock_eq_iff {u v : V} :
    bridgeBlock b E u = bridgeBlock b E v ↔ (bridgelessGraph b E).Reachable u v :=
  ConnectedComponent.eq

theorem bridgeBlock_eq_of_eq {u v : V} (h : b u = b v) : bridgeBlock b E u = bridgeBlock b E v := by
  rw [bridgeBlock_eq_iff]
  by_cases huv : u = v
  · exact huv ▸ Reachable.refl u
  · exact (bridgelessGraph_adj.2 (Or.inr (sameBlockGraph_adj.2 ⟨huv, h⟩))).reachable

theorem bridgeBlock_eq_of_adj_of_not_relBridges {u v : V} (h : E.Adj u v)
    (h' : ¬ (relBridges b E).Adj u v) : bridgeBlock b E u = bridgeBlock b E v :=
  bridgeBlock_eq_iff.2 (bridgelessGraph_adj.2 (Or.inl ⟨h, h'⟩)).reachable

theorem bridgelessGraph_le_sup : bridgelessGraph b E ≤ E ⊔ sameBlockGraph b :=
  sup_le_sup_right sdiff_le _

variable (hE : E ≤ crossBlockGraph b)
include hE

/-- Deleting a bridge `uv` keeps all non-bridge edges and all same-block edges. -/
theorem bridgelessGraph_le_deleteEdges {u v : V} (huv : (relBridges b E).Adj u v) :
    bridgelessGraph b E ≤ (E ⊔ sameBlockGraph b).deleteEdges {s(u, v)} := by
  intro x y hxy
  rw [deleteEdges_adj, Set.mem_singleton_iff]
  refine ⟨bridgelessGraph_le_sup hxy, fun he => ?_⟩
  rcases bridgelessGraph_adj.1 hxy with ⟨-, hnb⟩ | hsame
  · apply hnb
    rw [← mem_edgeSet, he, mem_edgeSet]
    exact huv
  · have hb := (sameBlockGraph_adj.1 hsame).2
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact crossBlockGraph_adj.1 (hE (relBridges_le huv)) hb
    · exact crossBlockGraph_adj.1 (hE (relBridges_le huv)) hb.symm

/-- The endpoints of a bridge lie in distinct bridge-blocks. -/
theorem bridgeBlock_ne_of_relBridges {u v : V} (huv : (relBridges b E).Adj u v) :
    bridgeBlock b E u ≠ bridgeBlock b E v := by
  intro h
  have hr := (bridgeBlock_eq_iff.1 h).mono (bridgelessGraph_le_deleteEdges hE huv)
  exact isBridge_iff.1 (relBridges_adj.1 huv).2 hr

/-- An edge of `E` is a bridge iff it joins two distinct bridge-blocks. -/
theorem relBridges_adj_iff {u v : V} :
    (relBridges b E).Adj u v ↔ E.Adj u v ∧ bridgeBlock b E u ≠ bridgeBlock b E v := by
  refine ⟨fun h => ⟨relBridges_le h, bridgeBlock_ne_of_relBridges hE h⟩, fun ⟨h, hne⟩ => ?_⟩
  by_contra hnb
  exact hne (bridgeBlock_eq_of_adj_of_not_relBridges h hnb)

/-- The bridges cross the bridge-blocks. -/
theorem relBridges_le_crossBlockGraph : relBridges b E ≤ crossBlockGraph (bridgeBlock b E) :=
  fun _ _ h => crossBlockGraph_adj.2 (bridgeBlock_ne_of_relBridges hE h)

/-- Deleting a bridge `uv` from the bridges, any walk of the bridge-tree that avoids the edge
`[u][v]` lifts to a walk of `G` avoiding `uv`. -/
theorem reachable_deleteEdges_of_reachable_bridgeTree {u v : V} (huv : (relBridges b E).Adj u v)
    {C D : (bridgelessGraph b E).ConnectedComponent}
    (hCD : ((bridgeTree b E).deleteEdges {s(bridgeBlock b E u, bridgeBlock b E v)}).Reachable C D)
    {x y : V} (hx : bridgeBlock b E x = C) (hy : bridgeBlock b E y = D) :
    ((E ⊔ sameBlockGraph b).deleteEdges {s(u, v)}).Reachable x y := by
  have hle : (bridgeTree b E).deleteEdges {s(bridgeBlock b E u, bridgeBlock b E v)} ≤
      blockQuotient (bridgeBlock b E) ((relBridges b E).deleteEdges {s(u, v)}) := by
    intro A B hAB
    rw [deleteEdges_adj, Set.mem_singleton_iff] at hAB
    obtain ⟨hne, p, q, hp, hq, hpq⟩ := blockQuotient_adj.1 hAB.1
    refine blockQuotient_adj.2 ⟨hne, p, q, hp, hq, ?_⟩
    rw [deleteEdges_adj, Set.mem_singleton_iff]
    refine ⟨hpq, fun he => hAB.2 ?_⟩
    rw [← hp, ← hq]
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Sym2.eq_swap
  have hlift := reachable_of_reachable_blockQuotient' (c := bridgeBlock b E)
    (H := bridgelessGraph b E) (K := (relBridges b E).deleteEdges {s(u, v)})
    (fun _ _ h => bridgeBlock_eq_iff.1 h) (hCD.mono hle) hx hy
  refine hlift.mono (sup_le (bridgelessGraph_le_deleteEdges hE huv) ?_)
  exact deleteEdges_mono (relBridges_le.trans le_sup_left)

/-- **Two bridge-blocks are joined by at most one bridge.** -/
theorem hasUniqueReps_relBridges : HasUniqueReps (bridgeBlock b E) (relBridges b E) := by
  intro A B hAB
  obtain ⟨hne, u, v, hu, hv, huv⟩ := blockQuotient_adj.1 hAB
  refine ⟨(u, v), ⟨hu, hv, huv⟩, ?_⟩
  rintro ⟨u', v'⟩ ⟨hu', hv', hu'v'⟩
  by_contra hp
  have hne' : s(u', v') ≠ s(u, v) := by
    intro he
    rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hp (Prod.ext h1 h2)
    · subst h1 h2
      exact hne (hu.symm.trans hv')
  -- a walk from `u` to `v` through `u' v'` avoiding `uv`
  have h1 : ((E ⊔ sameBlockGraph b).deleteEdges {s(u, v)}).Reachable u u' :=
    (bridgeBlock_eq_iff.1 (hu.trans hu'.symm)).mono (bridgelessGraph_le_deleteEdges hE huv)
  have h2 : ((E ⊔ sameBlockGraph b).deleteEdges {s(u, v)}).Adj u' v' := by
    rw [deleteEdges_adj, Set.mem_singleton_iff]
    exact ⟨Or.inl (relBridges_le hu'v'), hne'⟩
  have h3 : ((E ⊔ sameBlockGraph b).deleteEdges {s(u, v)}).Reachable v' v :=
    (bridgeBlock_eq_iff.1 (hv'.trans hv.symm)).mono (bridgelessGraph_le_deleteEdges hE huv)
  exact isBridge_iff.1 (relBridges_adj.1 huv).2 ((h1.trans h2.reachable).trans h3)

/-- **The bridge-tree is acyclic**: every edge of it is a bridge of it. -/
theorem bridgeTree_isAcyclic : (bridgeTree b E).IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro A B hAB
  obtain ⟨-, u, v, hu, hv, huv⟩ := blockQuotient_adj.1 hAB
  rw [isBridge_iff]
  intro hr
  subst hu hv
  exact isBridge_iff.1 (relBridges_adj.1 huv).2
    (reachable_deleteEdges_of_reachable_bridgeTree hE huv hr rfl rfl)

/-- Walks of `G` project to walks of the bridge-tree. -/
theorem reachable_bridgeTree_of_reachable {u v : V} (h : (E ⊔ sameBlockGraph b).Reachable u v) :
    (bridgeTree b E).Reachable (bridgeBlock b E u) (bridgeBlock b E v) := by
  refine reachable_comp_of_forall_adj (bridgeBlock b E) (fun x y hxy => ?_) h
  by_cases hb : (relBridges b E).Adj x y
  · exact (blockQuotient_adj_of_adj hb (bridgeBlock_ne_of_relBridges hE hb)).reachable
  · rcases hxy with hxy | hxy
    · rw [bridgeBlock_eq_of_adj_of_not_relBridges hxy hb]
    · rw [bridgeBlock_eq_of_eq (sameBlockGraph_adj.1 hxy).2]

/-- **The bridge-tree is a tree** when `G = E ∪ ℰ^intra` is connected (`E ∈ 𝖤^X`). -/
theorem bridgeTree_isTree (hG : (E ⊔ sameBlockGraph b).Connected) : (bridgeTree b E).IsTree := by
  refine ⟨?_, bridgeTree_isAcyclic hE⟩
  have : Nonempty V := hG.nonempty
  refine ⟨fun A B => ?_⟩
  induction A using ConnectedComponent.ind with
  | h u =>
    induction B using ConnectedComponent.ind with
    | h v => exact reachable_bridgeTree_of_reachable hE (hG.preconnected u v)

omit hE in
/-- Every edge of `E` that is not a bridge lies on a cycle of the bridgeless graph. -/
theorem not_isBridge_bridgelessGraph {a c : V} (hac : E.Adj a c)
    (hnb : ¬ (relBridges b E).Adj a c) : ¬ (bridgelessGraph b E).IsBridge s(a, c) := by
  have hG : ¬ (E ⊔ sameBlockGraph b).IsBridge s(a, c) := fun h => hnb (relBridges_adj.2 ⟨hac, h⟩)
  have hmem : s(a, c) ∈ (E ⊔ sameBlockGraph b).edgeSet := (mem_edgeSet _).2 (Or.inl hac)
  rw [isBridge_iff_forall_cycle_notMem hmem] at hG
  push Not at hG
  obtain ⟨w, p, hp, hep⟩ := hG
  have hsub : ∀ e ∈ p.edges, e ∈ (bridgelessGraph b E).edgeSet := by
    intro e he
    have heG := p.edges_subset_edgeSet he
    induction e using Sym2.ind with
    | _ x y =>
      rw [mem_edgeSet] at heG ⊢
      rcases heG with hxy | hxy
      · refine bridgelessGraph_adj.2 (Or.inl ⟨hxy, fun hb => ?_⟩)
        exact (relBridges_adj.1 hb).2.notMem_edges_of_isCycle hp he
      · exact bridgelessGraph_adj.2 (Or.inr hxy)
  intro hb
  exact hb.notMem_edges_of_isCycle (hp.transfer hsub) (by rwa [Walk.edges_transfer])

omit hE in
/-- **Bridge-blocks are 2-edge-connected**: deleting an inner edge `ac` of `E` (a non-bridge),
any two vertices of one bridge-block stay connected inside it. -/
theorem reachable_deleteEdges_of_bridgeBlock_eq {a c : V} (hac : E.Adj a c)
    (hnb : ¬ (relBridges b E).Adj a c) {x y : V} (hxy : bridgeBlock b E x = bridgeBlock b E y) :
    ((bridgelessGraph b E).deleteEdges {s(a, c)}).Reachable x y :=
  (bridgeBlock_eq_iff.1 hxy).reachable_deleteEdges_of_not_isBridge
    (not_isBridge_bridgelessGraph hac hnb)

omit hE in
/-- **Maximality of the bridge-blocks**: if `K ≤ G` is a graph in which no edge of `E` is a bridge
(e.g. the inner graph of a union of blocks which is 2-edge-connected relative to them), its
connected vertices lie in one bridge-block. -/
theorem bridgeBlock_eq_of_reachable_of_forall_not_isBridge {K : SimpleGraph V}
    (hK : K ≤ E ⊔ sameBlockGraph b) (hKb : ∀ x y, K.Adj x y → E.Adj x y → ¬ K.IsBridge s(x, y))
    {u v : V} (huv : K.Reachable u v) : bridgeBlock b E u = bridgeBlock b E v := by
  refine bridgeBlock_eq_iff.2 (huv.mono fun x y hxy => ?_)
  rcases hK hxy with hE' | hsame
  · refine bridgelessGraph_adj.2 (Or.inl ⟨hE', fun hb => ?_⟩)
    have hnb := hKb x y hxy hE'
    have hmem : s(x, y) ∈ K.edgeSet := (mem_edgeSet _).2 hxy
    rw [isBridge_iff_forall_cycle_notMem hmem] at hnb
    push Not at hnb
    obtain ⟨w, p, hp, hep⟩ := hnb
    exact (relBridges_adj.1 hb).2.notMem_edges_of_isCycle (hp.transfer (H := E ⊔ sameBlockGraph b)
      fun e he => edgeSet_mono hK (p.edges_subset_edgeSet he)) (by rwa [Walk.edges_transfer])
  · exact bridgelessGraph_adj.2 (Or.inr hsame)

end Bridges

end CoreForest

end MultipoleBKT

end
