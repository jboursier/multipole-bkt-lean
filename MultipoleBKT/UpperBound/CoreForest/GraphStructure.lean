/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.CoreForest.Core
public import MultipoleBKT.UpperBound.CoreForest.EulerOff

/-!
# Graph structure of the Eulerian graphs with exceptional vertices (Lemma 5.27)

The paper: Lemma 5.27 and its proof. Let `E ∈ Eulc^X(V_1^∞)` and `G = (V_X, E)`. Let `G_1, …, G_n` be the bridge-blocks
and `ℰ_br` the bridges of the 2-core of `G` relative to the surviving parts, and let `B_l` be the
set of multipoles contained in `G_l` or in a pendant tree attached to `G_l`. Then

1. a multipole `S` with `deg_E(S) = 1` contains a marked vertex (`lemma_5_27_1`, in
   `MultipoleBKT.UpperBound.CoreForest.EulerOff`);
2. if `n ≥ 2` and `G_l` is a leaf of the bridge-tree `(V_Y, ℰ_br)/Y`, then `B_l` contains a
   marked vertex (`lemma_5_27_2`); in fact an odd number of them (`lemma_5_27_2_odd`).

Formalization. With `b = [·]^X`: the core blocks are `twoCore b E`, the core edges
`coreEdges b E`, the bridge-blocks of the core are the values `l` of `bridgeBlock b (coreEdges b E)`
(the blocks outside the core are isolated there), and its bridge-tree is
`bridgeTree b (coreEdges b E)`. A leaf `l` is a vertex with exactly one neighbour in the
bridge-tree (a leaf has a neighbour, so `n ≥ 2` is automatic). The vertex set `V_{B_l}` is
`attachedSet b E l`: the vertices whose block is joined by pendant edges to a core block in `G_l`
(each pendant tree is attached at a single core block, `eq_of_reachable_pendant`).

The proof is the paper's: exactly one edge of `E` leaves `V_{B_l}`, the bridge of `G_l`
(`card_cutPairs_attachedSet`), and the parity of this cut (`odd_card_inter_of_card_cutPairs_eq_one`)
gives an odd number of marked vertices in `V_{B_l}`. Neither the connectedness of `E` nor
`V_1^∞ ≠ ∅` is needed.
-/

@[expose] public section

namespace MultipoleBKT

namespace CoreForest

open Finset SimpleGraph

section Generic

variable {V β : Type*} [Fintype V] [Fintype β] [DecidableEq β] {b : V → β}
  {E : SimpleGraph V}

variable (b E) in
open scoped Classical in
/-- `V_{B_l}` (Lemma 5.27): the vertices whose block is joined by pendant edges to a core block of
the bridge-block `l` of the 2-core (the blocks of `G_l` and of the pendant trees attached to it). -/
noncomputable def attachedSet (l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent) :
    Finset V :=
  univ.filter fun x => ∃ y, bridgeBlock b (coreEdges b E) y = l ∧ b y ∈ twoCore b E ∧
    (blockQuotient b (pendantEdges b E)).Reachable (b x) (b y)

theorem mem_attachedSet {l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent} {x : V} :
    x ∈ attachedSet b E l ↔ ∃ y, bridgeBlock b (coreEdges b E) y = l ∧ b y ∈ twoCore b E ∧
      (blockQuotient b (pendantEdges b E)).Reachable (b x) (b y) := by
  classical
  simp [attachedSet]

/-- `V_{B_l}` is a union of blocks. -/
theorem mem_attachedSet_of_eq {l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent}
    {x x' : V} (hx : x ∈ attachedSet b E l) (h : b x = b x') : x' ∈ attachedSet b E l := by
  rw [mem_attachedSet] at hx ⊢
  rwa [← h]

open scoped Classical in
/-- **Exactly one edge of `E` leaves `V_{B_l}`** for a leaf `l` of the bridge-tree of the 2-core:
the bridge of `G_l`. -/
theorem card_cutPairs_attachedSet [DecidableEq V] (hE : E ≤ crossBlockGraph b)
    {l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent}
    (hl : ∃! m, (bridgeTree b (coreEdges b E)).Adj l m) :
    (cutPairs E (attachedSet b E l)).card = 1 := by
  have hEc : coreEdges b E ≤ crossBlockGraph b := coreEdges_le.trans hE
  obtain ⟨m, hlm, hm⟩ := hl
  obtain ⟨⟨u, v⟩, ⟨hu, hv, huv⟩, huniq⟩ := hasUniqueReps_relBridges hEc l m hlm
  have hlm' : l ≠ m := (blockQuotient_adj.1 hlm).1
  have huvc : (coreEdges b E).Adj u v := relBridges_le huv
  have hucore := (coreEdges_adj.1 huvc).2.1
  have hvcore := (coreEdges_adj.1 huvc).2.2
  rw [Finset.card_eq_one]
  refine ⟨(u, v), Finset.ext fun ⟨x, y⟩ => ?_⟩
  rw [mem_cutPairs, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hy, hxy⟩
    obtain ⟨y₀, hy₀l, hy₀c, hxy₀⟩ := mem_attachedSet.1 hx
    have hcross : b x ≠ b y := crossBlockGraph_adj.1 (hE hxy)
    rw [← coreEdges_sup_pendantEdges (b := b) (E := E)] at hxy
    rcases hxy with hc | hp
    · obtain ⟨-, hxc, hyc⟩ := coreEdges_adj.1 hc
      have hxl : bridgeBlock b (coreEdges b E) x = l := by
        rw [bridgeBlock_eq_of_eq (eq_of_reachable_pendant hxc hy₀c hxy₀), hy₀l]
      have hyl : bridgeBlock b (coreEdges b E) y ≠ l := fun h =>
        hy (mem_attachedSet.2 ⟨y, h, hyc, Reachable.refl _⟩)
      have hbr : (relBridges b (coreEdges b E)).Adj x y :=
        (relBridges_adj_iff hEc).2 ⟨hc, hxl ▸ fun h => hyl h.symm⟩
      have hym : bridgeBlock b (coreEdges b E) y = m := by
        refine hm _ ?_
        rw [← hxl]
        exact blockQuotient_adj_of_adj hbr (bridgeBlock_ne_of_relBridges hEc hbr)
      exact huniq (x, y) ⟨hxl, hym, hbr⟩
    · exfalso
      refine hy (mem_attachedSet.2 ⟨y₀, hy₀l, hy₀c, ?_⟩)
      exact (blockQuotient_adj_of_adj hp.symm (Ne.symm hcross)).reachable.trans hxy₀
  · rintro h
    rw [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨mem_attachedSet.2 ⟨x, hu, hucore, Reachable.refl _⟩, fun hy => ?_,
      coreEdges_le huvc⟩
    obtain ⟨y₀, hy₀l, hy₀c, hyy₀⟩ := mem_attachedSet.1 hy
    have : bridgeBlock b (coreEdges b E) y = l := by
      rw [bridgeBlock_eq_of_eq (eq_of_reachable_pendant hvcore hy₀c hyy₀), hy₀l]
    exact hlm' (this.symm.trans hv)

end Generic

section Lemma

variable {X : Finset (Finset ℕ)}

open scoped Classical in
/-- **Lemma 5.27 (2)**, with the
conclusion of the proof: for `E ∈ Eul^X(V_1^∞)` and a leaf `l` of the bridge-tree of the 2-core of
`(V_X, E)` relative to the surviving parts of `X`, the vertex set of `B_l` (the multipoles of `G_l`
and of the pendant trees attached to it) contains an odd number of marked vertices. -/
theorem lemma_5_27_2_odd (hX : IsSubpartition X) {V₁ : Finset (X.biUnion id)}
    {E : SimpleGraph (X.biUnion id)} (hE : IsRelEulerianOff X V₁ E)
    {l : (bridgelessGraph (blockOf hX) (coreEdges (blockOf hX) E)).ConnectedComponent}
    (hl : ∃! m, (bridgeTree (blockOf hX) (coreEdges (blockOf hX) E)).Adj l m) :
    Odd (attachedSet (blockOf hX) E l ∩ V₁).card := by
  have hcross : E ≤ crossBlockGraph (blockOf hX) := interEdges_eq hX ▸ hE.1
  exact odd_card_inter_of_card_cutPairs_eq_one hX hE
    (fun i hi j hij => mem_attachedSet_of_eq hi hij) (card_cutPairs_attachedSet hcross hl)

/-- **Lemma 5.27 (2)**: `B_l ∩ X_1^∞ ≠ ∅` for a leaf `G_l`
of the bridge-tree of the 2-core, i.e. some multipole of `G_l` or of a pendant tree attached to it
contains a marked vertex. The hypotheses `E ∈ 𝖤^X` and `V_1^∞ ≠ ∅` of the paper are not
needed. -/
theorem lemma_5_27_2 (hX : IsSubpartition X) {V₁ : Finset (X.biUnion id)}
    {E : SimpleGraph (X.biUnion id)} (hE : IsRelEulerianOff X V₁ E)
    {l : (bridgelessGraph (blockOf hX) (coreEdges (blockOf hX) E)).ConnectedComponent}
    (hl : ∃! m, (bridgeTree (blockOf hX) (coreEdges (blockOf hX) E)).Adj l m) :
    ∃ i ∈ V₁, ∃ y, bridgeBlock (blockOf hX) (coreEdges (blockOf hX) E) y = l ∧
      blockOf hX y ∈ twoCore (blockOf hX) E ∧
      (blockQuotient (blockOf hX) (pendantEdges (blockOf hX) E)).Reachable (blockOf hX i)
        (blockOf hX y) := by
  classical
  obtain ⟨i, hi⟩ := Finset.card_pos.1 (lemma_5_27_2_odd hX hE hl).pos
  rw [Finset.mem_inter] at hi
  exact ⟨i, hi.2, mem_attachedSet.1 hi.1⟩

end Lemma

end CoreForest

end MultipoleBKT

end
