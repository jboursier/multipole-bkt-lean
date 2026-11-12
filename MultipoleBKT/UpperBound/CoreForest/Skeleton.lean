/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.CoreForest.GraphStructure

/-!
# Peeling into a minimal skeleton (Definition 5.28) and the parity of the marks

The paper: Definition 5.28 and
the first paragraph of the proof of Corollary 5.34: "peeling preserves every
bridge cut of `E_0`; summing its parity condition over a leaf block shows that this block contains
an odd number of elements of `V_1^∞`".

As in `MultipoleBKT.UpperBound.CoreForest.GraphStructure`, `b : V → β` is a block map,
`E ≤ crossBlockGraph b`, the core edges are `coreEdges b E` and the bridge-blocks of the core are
the values of `bridgeBlock b (coreEdges b E)`.

* `blockInnerEdges b E l`: the edges of the bridge-block `G_l` of the core (its non-bridge core
  edges);
* `TwoEdgeConnectsBlock b E l K`: `K` (with the same-block edges) connects the vertices of `G_l`,
  also after deleting any one edge of `K`: `K` is spanning and 2-edge-connected relative to the
  blocks `X_l` of `G_l`;
* `IsBlockSkeleton b E l K`: `K` is an admissible `G_l'`, an inclusion-minimal such subgraph of
  `G_l`; for a block consisting of one part, `G_l` has no edge and `K = ∅`, as the paper
  prescribes;
* `IsMinimalSkeleton b E E'`: `E'` is an admissible value of `Peeled_X(E)`:
  `E' = ⋃_l E(G_l') ∪ ⋃_i E(P_i) ∪ ℰ_br`. The paper selects each `G_l'` "according to
  lexicographical order", an order on edge sets which it does not specify; as in
  `MultipoleBKT.Peeling.IsPeeledSkeleton` (Definition 4.38), the admissible choices form a
  predicate and the results hold for every admissible choice, in particular the paper's.
  `E` is a minimal skeleton when `IsMinimalSkeleton b E E`.

Results:

* `exists_isMinimalSkeleton`: `Peeled_X(E)` exists (`G_l` itself is 2-edge-connected, by
  `reachable_deleteEdges_of_bridgeBlock_eq`);
* `IsMinimalSkeleton.le`: `Peeled_X(E) ⊆ E`;
* `IsMinimalSkeleton.bridgeBlock_eq`: each bridge-block of the core of `E` lies in one bridge-block
  of `E' = Peeled_X(E)`;
* `card_cutPairs_bridgeBlock_of_leaf`: a leaf bridge-block of any `E` is left by exactly one edge
  of `E`;
* `IsMinimalSkeleton.cutPairs_eq`: peeling preserves every bridge cut;
* `odd_card_marks_of_leaf`: **parity of the marks** (Corollary 5.34): for
  `E_0 ∈ Eul^X(V_1^∞)` and `E = Peeled_X(E_0)`, every leaf of the bridge-tree of the full quotient
  of `(V_X, E)` (pendant blocks included) contains an odd number of marked vertices.
-/

@[expose] public section

namespace MultipoleBKT

namespace CoreForest

open Finset SimpleGraph

section Skeleton

variable {V β : Type*} [Fintype V] [Fintype β] [DecidableEq β] (b : V → β) (E : SimpleGraph V)

/-- The edges of the bridge-block `G_l` of the 2-core: the non-bridge core edges inside `l`. -/
def blockInnerEdges (l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent) :
    SimpleGraph V :=
  (coreEdges b E \ relBridges b (coreEdges b E)) ⊓
    SimpleGraph.fromRel fun u _ => bridgeBlock b (coreEdges b E) u = l

/-- `K` spans the bridge-block `l` of the core and is 2-edge-connected on it relative to its
blocks: with the same-block edges, `K` connects any two vertices of `l`, also after deleting any one
edge of `K`. -/
def TwoEdgeConnectsBlock (l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent)
    (K : SimpleGraph V) : Prop :=
  (∀ x y, bridgeBlock b (coreEdges b E) x = l → bridgeBlock b (coreEdges b E) y = l →
      (K ⊔ sameBlockGraph b).Reachable x y) ∧
    ∀ a c, K.Adj a c → ∀ x y, bridgeBlock b (coreEdges b E) x = l →
      bridgeBlock b (coreEdges b E) y = l →
        (K.deleteEdges {s(a, c)} ⊔ sameBlockGraph b).Reachable x y

/-- `K` is an admissible `G_l'` (Definition 5.28): an inclusion-minimal spanning subgraph of the
bridge-block `G_l` which is 2-edge-connected relative to the blocks of `G_l`. -/
def IsBlockSkeleton (l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent)
    (K : SimpleGraph V) : Prop :=
  K ≤ blockInnerEdges b E l ∧ TwoEdgeConnectsBlock b E l K ∧
    ∀ K' ≤ K, TwoEdgeConnectsBlock b E l K' → K' = K

/-- `E'` is an admissible value of `Peeled_X(E)` (Definition 5.28): the union of
admissible skeletons `G_l'` of the bridge-blocks of the 2-core, of the pendant trees and of the
bridges of the 2-core. -/
def IsMinimalSkeleton (E' : SimpleGraph V) : Prop :=
  ∃ Ks : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → SimpleGraph V,
    (∀ l, IsBlockSkeleton b E l (Ks l)) ∧
      E' = (⨆ l, Ks l) ⊔ pendantEdges b E ⊔ relBridges b (coreEdges b E)

variable {b E}

theorem blockInnerEdges_adj {l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent}
    {u v : V} :
    (blockInnerEdges b E l).Adj u v ↔ (coreEdges b E).Adj u v ∧
      ¬ (relBridges b (coreEdges b E)).Adj u v ∧ bridgeBlock b (coreEdges b E) u = l := by
  rw [blockInnerEdges, inf_adj, sdiff_adj, fromRel_adj]
  constructor
  · rintro ⟨⟨h, hnb⟩, -, hu | hv⟩
    · exact ⟨h, hnb, hu⟩
    · exact ⟨h, hnb, (bridgeBlock_eq_of_adj_of_not_relBridges h hnb).trans hv⟩
  · rintro ⟨h, hnb, hu⟩
    exact ⟨⟨h, hnb⟩, h.ne, Or.inl hu⟩

omit [Fintype V] [Fintype β] [DecidableEq β] in
/-- Walks of a subgraph of the bridgeless graph stay inside a bridge-block, and can be read in any
graph containing their edges there. -/
theorem reachable_of_reachable_of_bridgeBlock {H K : SimpleGraph V} {B : SimpleGraph V}
    (hH : H ≤ bridgelessGraph b B) {l : (bridgelessGraph b B).ConnectedComponent}
    (hHK : ∀ u v, H.Adj u v → bridgeBlock b B u = l → K.Adj u v) {x y : V}
    (h : H.Reachable x y) (hx : bridgeBlock b B x = l) : K.Reachable x y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.refl _
  | @cons x z y hxz q ih =>
    have hz : bridgeBlock b B z = l := (bridgeBlock_eq_iff.2 (hH hxz).reachable).symm.trans hx
    exact (hHK x z hxz hx).reachable.trans (ih hz)

/-- The bridge-block `G_l` itself spans `l` 2-edge-connectedly. -/
theorem twoEdgeConnectsBlock_blockInnerEdges
    (l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent) :
    TwoEdgeConnectsBlock b E l (blockInnerEdges b E l) := by
  constructor
  · intro x y hx hy
    refine reachable_of_reachable_of_bridgeBlock le_rfl (fun u v huv hu => ?_)
      (bridgeBlock_eq_iff.1 (hx.trans hy.symm)) hx
    rcases bridgelessGraph_adj.1 huv with ⟨h, hnb⟩ | hs
    · exact Or.inl (blockInnerEdges_adj.2 ⟨h, hnb, hu⟩)
    · exact Or.inr hs
  · intro a c hac x y hx hy
    obtain ⟨hc, hnb, -⟩ := blockInnerEdges_adj.1 hac
    refine reachable_of_reachable_of_bridgeBlock (deleteEdges_le _) (fun u v huv hu => ?_)
      (reachable_deleteEdges_of_bridgeBlock_eq hc hnb (hx.trans hy.symm)) hx
    rw [deleteEdges_adj] at huv
    rcases bridgelessGraph_adj.1 huv.1 with ⟨h, hnb'⟩ | hs
    · exact Or.inl (deleteEdges_adj.2 ⟨blockInnerEdges_adj.2 ⟨h, hnb', hu⟩, huv.2⟩)
    · exact Or.inr hs

/-- **`Peeled_X(E)` exists**: every bridge-block of the core has an admissible skeleton. -/
theorem exists_isMinimalSkeleton [DecidableEq V] : ∃ E', IsMinimalSkeleton b E E' := by
  have hex : ∀ l, ∃ K, IsBlockSkeleton b E l K := by
    intro l
    obtain ⟨K, ⟨hle, h2⟩, hmin⟩ := WellFounded.has_min wellFounded_lt
      {K : SimpleGraph V | K ≤ blockInnerEdges b E l ∧ TwoEdgeConnectsBlock b E l K}
      ⟨_, le_rfl, twoEdgeConnectsBlock_blockInnerEdges l⟩
    refine ⟨K, hle, h2, fun K' hK' h2' => ?_⟩
    by_contra hne
    exact hmin K' ⟨hK'.trans hle, h2'⟩ (lt_of_le_of_ne hK' hne)
  choose Ks hKs using hex
  exact ⟨_, Ks, hKs, rfl⟩

/-- `Peeled_X(E) ⊆ E`. -/
theorem IsMinimalSkeleton.le {E' : SimpleGraph V} (h : IsMinimalSkeleton b E E') : E' ≤ E := by
  obtain ⟨Ks, hKs, rfl⟩ := h
  refine sup_le (sup_le (iSup_le fun l => ?_) pendantEdges_le)
    (relBridges_le.trans coreEdges_le)
  exact fun u v huv => coreEdges_le (blockInnerEdges_adj.1 ((hKs l).1 huv)).1

/-- The skeleton keeps the pendant edges and the bridges of the core. -/
theorem IsMinimalSkeleton.adj_of_not_inner {E' : SimpleGraph V} (h : IsMinimalSkeleton b E E')
    {u v : V} (huv : E.Adj u v)
    (hin : ¬ ((coreEdges b E).Adj u v ∧ ¬ (relBridges b (coreEdges b E)).Adj u v)) :
    E'.Adj u v := by
  obtain ⟨Ks, -, rfl⟩ := h
  by_cases hc : (coreEdges b E).Adj u v
  · exact Or.inr (not_and_not_right.1 hin hc)
  · exact Or.inl (Or.inr (pendantEdges_adj.2 ⟨huv, by
      by_contra h'
      push Not at h'
      exact hc (coreEdges_adj.2 ⟨huv, h'⟩)⟩))

/-- **`E` is a minimal skeleton** (`Peeled_X(E) = E`) iff every bridge-block `G_l` of its core is its
own skeleton: then the skeletons are forced, `G_l' = G_l`. -/
theorem isMinimalSkeleton_self_iff :
    IsMinimalSkeleton b E E ↔ ∀ l, IsBlockSkeleton b E l (blockInnerEdges b E l) := by
  constructor
  · rintro ⟨Ks, hKs, hE⟩
    have hKl : ∀ l, Ks l = blockInnerEdges b E l := by
      intro l
      refine le_antisymm (hKs l).1 fun u v huv => ?_
      obtain ⟨hc, hnb, hu⟩ := blockInnerEdges_adj.1 huv
      have huvE : E.Adj u v := coreEdges_le hc
      rw [hE] at huvE
      rcases huvE with (h | h) | h
      · obtain ⟨l', hl'⟩ := (iSup_adj).1 h
        have hu' := (blockInnerEdges_adj.1 ((hKs l').1 hl')).2.2
        rw [hu'] at hu
        exact hu ▸ hl'
      · exact absurd (pendantEdges_adj.1 h).2
          (by rw [coreEdges_adj] at hc; push Not; exact ⟨hc.2.1, hc.2.2⟩)
      · exact absurd h hnb
    intro l
    rw [← hKl l]
    exact hKs l
  · intro h
    refine ⟨fun l => blockInnerEdges b E l, h, ?_⟩
    ext u v
    simp only [sup_adj, iSup_adj]
    constructor
    · intro huv
      by_cases hc : (coreEdges b E).Adj u v
      · by_cases hb : (relBridges b (coreEdges b E)).Adj u v
        · exact Or.inr hb
        · exact Or.inl (Or.inl ⟨_, blockInnerEdges_adj.2 ⟨hc, hb, rfl⟩⟩)
      · exact Or.inl (Or.inr ((sdiff_adj _ _ _ _).2 ⟨huv, hc⟩))
    · rintro ((⟨l, hl⟩ | hp) | hb)
      · exact coreEdges_le (blockInnerEdges_adj.1 hl).1
      · exact pendantEdges_le hp
      · exact coreEdges_le (relBridges_le hb)

variable (hE : E ≤ crossBlockGraph b)
include hE

/-- **Each bridge-block of the core of `E` lies in one bridge-block of `Peeled_X(E)`.** -/
theorem IsMinimalSkeleton.bridgeBlock_eq {E' : SimpleGraph V} (h : IsMinimalSkeleton b E E')
    {x y : V} (hxy : bridgeBlock b (coreEdges b E) x = bridgeBlock b (coreEdges b E) y) :
    bridgeBlock b E' x = bridgeBlock b E' y := by
  have hE' : E' ≤ crossBlockGraph b := h.le.trans hE
  obtain ⟨Ks, hKs, hE'eq⟩ := h
  set l := bridgeBlock b (coreEdges b E) x
  have hKE' : Ks l ≤ E' := by
    rw [hE'eq]
    exact (le_iSup Ks l).trans (le_sup_left.trans le_sup_left)
  -- the edges of `Ks l` are not bridges of `E'`
  have hstep : ∀ u v, (Ks l ⊔ sameBlockGraph b).Adj u v → bridgeBlock b E' u = bridgeBlock b E' v := by
    intro u v huv
    rcases huv with hK | hs
    · refine bridgeBlock_eq_of_adj_of_not_relBridges (hKE' hK) fun hb => ?_
      obtain ⟨hc, hnb, hu⟩ := blockInnerEdges_adj.1 ((hKs l).1 hK)
      have hv : bridgeBlock b (coreEdges b E) v = l :=
        (bridgeBlock_eq_of_adj_of_not_relBridges hc hnb).symm.trans hu
      have hr := (hKs l).2.1.2 u v hK u v hu hv
      refine isBridge_iff.1 (relBridges_adj.1 hb).2 (hr.mono fun p q hpq => ?_)
      rw [deleteEdges_adj, Set.mem_singleton_iff]
      rcases hpq with hpq | hpq
      · rw [deleteEdges_adj, Set.mem_singleton_iff] at hpq
        exact ⟨Or.inl (hKE' hpq.1), hpq.2⟩
      · refine ⟨Or.inr hpq, fun he => ?_⟩
        have hb' := (sameBlockGraph_adj.1 hpq).2
        have hcr := crossBlockGraph_adj.1 (hE' (hKE' hK))
        rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hcr hb'
        · exact hcr hb'.symm
    · exact bridgeBlock_eq_of_eq (sameBlockGraph_adj.1 hs).2
  obtain ⟨p⟩ := (hKs l).2.1.1 x y rfl hxy.symm
  clear hE'eq
  induction p with
  | nil => rfl
  | cons h q ih => exact (hstep _ _ h).trans (ih hxy)

omit hE [Fintype β] [DecidableEq β] in
open scoped Classical in
/-- A leaf of the bridge-tree of `E` is left by exactly one edge of `E`. -/
theorem card_cutPairs_bridgeBlock_of_leaf [DecidableEq V] [DecidableRel E.Adj]
    (hE : E ≤ crossBlockGraph b) {l : (bridgelessGraph b E).ConnectedComponent}
    (hl : ∃! m, (bridgeTree b E).Adj l m) :
    (cutPairs E (univ.filter fun x => bridgeBlock b E x = l)).card = 1 := by
  obtain ⟨m, hlm, hm⟩ := hl
  obtain ⟨⟨u, v⟩, ⟨hu, hv, huv⟩, huniq⟩ := hasUniqueReps_relBridges hE l m hlm
  have hlm' : l ≠ m := (blockQuotient_adj.1 hlm).1
  rw [Finset.card_eq_one]
  refine ⟨(u, v), Finset.ext fun ⟨x, y⟩ => ?_⟩
  rw [mem_cutPairs, Finset.mem_singleton, Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨⟨-, hx⟩, hy, hxy⟩
    have hy' : bridgeBlock b E y ≠ l := fun h => hy ⟨Finset.mem_univ _, h⟩
    have hbr : (relBridges b E).Adj x y := (relBridges_adj_iff hE).2 ⟨hxy, hx ▸ fun h => hy' h.symm⟩
    have hym : bridgeBlock b E y = m := by
      refine hm _ ?_
      rw [← hx]
      exact blockQuotient_adj_of_adj hbr (bridgeBlock_ne_of_relBridges hE hbr)
    exact huniq (x, y) ⟨hx, hym, hbr⟩
  · intro h
    rw [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨Finset.mem_univ _, hu⟩, fun h => hlm' (h.2.symm.trans hv), relBridges_le huv⟩

/-- **Peeling preserves the bridge cuts**: for a union `U` of bridge-blocks of `E' = Peeled_X(E)`,
the edges of `E` leaving `U` are those of `E'`. -/
theorem IsMinimalSkeleton.cutPairs_eq [DecidableEq V] [DecidableRel E.Adj] {E' : SimpleGraph V}
    [DecidableRel E'.Adj] (h : IsMinimalSkeleton b E E') {U : Finset V}
    (hU : ∀ x ∈ U, ∀ y, bridgeBlock b E' x = bridgeBlock b E' y → y ∈ U) :
    cutPairs E U = cutPairs E' U := by
  ext ⟨x, y⟩
  rw [mem_cutPairs, mem_cutPairs]
  refine ⟨fun ⟨hx, hy, hxy⟩ => ⟨hx, hy, ?_⟩, fun ⟨hx, hy, hxy⟩ => ⟨hx, hy, h.le hxy⟩⟩
  by_contra hne
  have hin : (coreEdges b E).Adj x y ∧ ¬ (relBridges b (coreEdges b E)).Adj x y := by
    by_contra hin
    exact hne (h.adj_of_not_inner hxy hin)
  exact hy (hU x hx y (h.bridgeBlock_eq hE
    (bridgeBlock_eq_of_adj_of_not_relBridges hin.1 hin.2)))

end Skeleton

section Marks

variable {X : Finset (Finset ℕ)}

open scoped Classical in
/-- **Parity of the marks** (proof of Corollary 5.34):
for `E_0 ∈ Eul^X(V_1^∞)` and an admissible `E = Peeled_X(E_0)`, every leaf `l` of the bridge-tree
of the full multigraph quotient of `(V_X, E)` (its bridge-blocks, pendant singletons included)
contains an odd number of marked vertices. -/
theorem odd_card_marks_of_leaf (hX : IsSubpartition X) {V₁ : Finset (X.biUnion id)}
    {E₀ E : SimpleGraph (X.biUnion id)} (hE₀ : IsRelEulerianOff X V₁ E₀)
    (hE : IsMinimalSkeleton (blockOf hX) E₀ E)
    {l : (bridgelessGraph (blockOf hX) E).ConnectedComponent}
    (hl : ∃! m, (bridgeTree (blockOf hX) E).Adj l m) :
    Odd ((univ.filter fun x => bridgeBlock (blockOf hX) E x = l) ∩ V₁).card := by
  have hcross₀ : E₀ ≤ crossBlockGraph (blockOf hX) := interEdges_eq hX ▸ hE₀.1
  have hcross : E ≤ crossBlockGraph (blockOf hX) := hE.le.trans hcross₀
  have hU : ∀ x ∈ univ.filter (fun x => bridgeBlock (blockOf hX) E x = l), ∀ y,
      bridgeBlock (blockOf hX) E x = bridgeBlock (blockOf hX) E y →
        y ∈ univ.filter (fun x => bridgeBlock (blockOf hX) E x = l) := by
    intro x hx y hxy
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_univ _, hxy.symm.trans hx.2⟩
  refine odd_card_inter_of_card_cutPairs_eq_one hX hE₀
    (fun x hx y hxy => hU x hx y (bridgeBlock_eq_of_eq hxy)) ?_
  rw [hE.cutPairs_eq hcross₀ hU]
  exact card_cutPairs_bridgeBlock_of_leaf hcross hl

end Marks

end CoreForest

end MultipoleBKT

end
