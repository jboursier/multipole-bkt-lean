/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.CoreForest.Core

/-!
# The pendant trees are trees (Definitions 5.25 (2), 5.26 (2))

The paper: Definition 5.25 (2) and Definition 5.26 (2)
: outside the 2-core, `G` is an edge-disjoint union of pendant trees, each attached
to the core at one multipole; if the core is empty, `G` is the only pendant tree. These claims are
stated without proof in the paper.

As in `MultipoleBKT.UpperBound.CoreForest.Core`, `b : V → β` is a block map and
`E ≤ crossBlockGraph b`.

* `pendantEdges_le_relBridges`: every pendant edge is a bridge of `G = E ∪ ℰ^intra`. Otherwise its
  bridge-block (in `MultipoleBKT.UpperBound.CoreForest.Bridges`) would contain at least two blocks,
  each with two inner edges (2-edge-connectivity), and these blocks together with the core would
  form a `2`-closed family larger than the core.
* `isRelForest_pendantEdges`: hence the pendant edges form a forest relative to the blocks: their
  quotient is acyclic and each quotient edge comes from a single edge
  (`isAcyclic_blockQuotient_pendantEdges`, `hasUniqueReps_pendantEdges`). Together with
  `eq_of_reachable_pendant` (one core block per pendant component) and `exists_attachment` (every
  block is attached when `G` is connected), this is the decomposition of `G` into its 2-core and
  edge-disjoint pendant trees (`coreEdges_sup_pendantEdges`).
* `isRelTree₀_of_twoCore_eq_empty`: for a subpartition `X` and `E ∈ 𝖤_0^X` with empty core, `G` is
  the only pendant tree: `E ∈ 𝖳_0^X`.
-/

@[expose] public section

namespace MultipoleBKT

namespace CoreForest

open Finset SimpleGraph

/-- A bridge of `G` is a bridge of every subgraph containing it. -/
theorem IsBridge.anti {V : Type*} {G H : SimpleGraph V} (hHG : H ≤ G) {u v : V}
    (h : G.IsBridge s(u, v)) : H.IsBridge s(u, v) := by
  rw [isBridge_iff] at h ⊢
  exact fun hr => h (hr.mono (deleteEdges_mono hHG))

section Pendant

variable {V β : Type*} [Fintype V] [Fintype β] [DecidableEq β] {b : V → β} {E : SimpleGraph V}

omit [Fintype V] [Fintype β] [DecidableEq β] in
/-- A walk, in a subgraph `G` of the bridgeless graph, from `z` to a vertex of another block leaves
the block of `z` through a non-bridge edge `(p, q)` of `E` lying in `G`, with `q` reachable from
`z` in `G`. -/
theorem exists_boundary_edge {G : SimpleGraph V} (hG : G ≤ bridgelessGraph b E) {z w : V}
    (hzw : G.Reachable z w) (hw : b w ≠ b z) :
    ∃ p q, G.Adj p q ∧ b p = b z ∧ b q ≠ b z ∧ E.Adj p q ∧ ¬ (relBridges b E).Adj p q ∧
      G.Reachable z q := by
  obtain ⟨W⟩ := hzw
  obtain ⟨d, hd, hd1, hd2⟩ := W.exists_boundary_dart {v | b v = b z} rfl hw
  simp only [Set.mem_ofPred_eq] at hd1 hd2
  have hadj := hG d.adj
  rcases bridgelessGraph_adj.1 hadj with ⟨hE, hnb⟩ | hsame
  · refine ⟨d.fst, d.snd, d.adj, hd1, hd2, hE, hnb, ?_⟩
    classical
    exact (W.takeUntil d.snd (W.dart_snd_mem_support_of_mem_darts hd)).reachable
  · exact absurd ((sameBlockGraph_adj.1 hsame).2.symm.trans hd1) hd2

variable (hE : E ≤ crossBlockGraph b)
include hE

/-- **Every pendant edge is a bridge** of `G = E ∪ ℰ^intra`. -/
theorem pendantEdges_le_relBridges : pendantEdges b E ≤ relBridges b E := by
  classical
  intro x y hxy
  obtain ⟨hExy, hout⟩ := pendantEdges_adj.1 hxy
  by_contra hnb
  set K := bridgeBlock b E x with hK
  have hyK : bridgeBlock b E y = K := (bridgeBlock_eq_of_adj_of_not_relBridges hExy hnb).symm
  set F := twoCore b E ∪ univ.filter (fun S => ∃ z, b z = S ∧ bridgeBlock b E z = K) with hF
  have hmemF : ∀ {z : V}, bridgeBlock b E z = K → b z ∈ F := fun {z} hz =>
    Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, z, rfl, hz⟩)
  have hcross : b x ≠ b y := crossBlockGraph_adj.1 (hE hExy)
  have hclosed : IsTwoClosed b E F := by
    intro S hS
    rcases Finset.mem_union.1 hS with hSc | hSK
    · exact (isTwoClosed_twoCore S hSc).trans (degIn_mono Finset.subset_union_left S)
    obtain ⟨z, rfl, hzK⟩ := (Finset.mem_filter.1 hSK).2
    -- a vertex of the bridge-block outside the block of `z`
    obtain ⟨w, hwK, hwz⟩ : ∃ w, bridgeBlock b E w = K ∧ b w ≠ b z := by
      by_cases hxz : b x = b z
      · exact ⟨y, hyK, fun h => hcross (hxz.trans h.symm)⟩
      · exact ⟨x, rfl, hxz⟩
    have hzw : (bridgelessGraph b E).Reachable z w := bridgeBlock_eq_iff.1 (hzK.trans hwK.symm)
    obtain ⟨p, q, hpq, hp, hq, hEpq, hnbpq, hzq⟩ := exists_boundary_edge le_rfl hzw hwz
    -- a second inner edge, avoiding `pq`
    have hpq' : ((bridgelessGraph b E).deleteEdges {s(p, q)}).Reachable p q :=
      reachable_deleteEdges_of_bridgeBlock_eq hEpq hnbpq (bridgeBlock_eq_iff.2 hpq.reachable)
    obtain ⟨p', q', hp'q', hp', hq', hEp'q', -, hpq''⟩ :=
      exists_boundary_edge (deleteEdges_le _) hpq' (hp ▸ hq)
    have hqK : bridgeBlock b E q = K := (bridgeBlock_eq_iff.2 hzq).symm.trans hzK
    have hpK : bridgeBlock b E p = K := (bridgeBlock_eq_iff.2 hpq.reachable).trans hqK
    have hq'K : bridgeBlock b E q' = K :=
      (bridgeBlock_eq_iff.2 (hpq''.mono (deleteEdges_le _))).symm.trans hpK
    unfold degIn
    rw [Nat.succ_le_iff, Finset.one_lt_card]
    refine ⟨(p, q), ?_, (p', q'), ?_, fun he => ?_⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hp, hmemF hqK, hEpq⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hp.symm ▸ hp', hmemF hq'K, hEp'q'⟩
    · rw [deleteEdges_adj, Set.mem_singleton_iff] at hp'q'
      apply hp'q'.2
      rw [Prod.mk.injEq] at he
      rw [he.1, he.2]
  have hsub := subset_twoCore hclosed
  rcases hout with h | h
  · exact h (hsub (hmemF rfl))
  · exact h (hsub (hmemF hyK))

/-- The pendant edges form a forest relative to the blocks: no pendant edge `uv` has its ends
joined by the other pendant edges and the same-block edges. -/
theorem isRelForest_pendantEdges : IsRelForest (sameBlockGraph b) (pendantEdges b E) := by
  intro u v huv hr
  have hbr := (relBridges_adj.1 (pendantEdges_le_relBridges hE huv)).2
  refine isBridge_iff.1 hbr (hr.mono fun x y hxy => ?_)
  rw [deleteEdges_adj, Set.mem_singleton_iff]
  rcases hxy with hs | hp
  · refine ⟨Or.inr hs, fun he => ?_⟩
    have hb := (sameBlockGraph_adj.1 hs).2
    have hcross := crossBlockGraph_adj.1 (hE (pendantEdges_le huv))
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcross hb
    · exact hcross hb.symm
  · rw [deleteEdges_adj, Set.mem_singleton_iff] at hp
    exact ⟨Or.inl (pendantEdges_le hp.1), hp.2⟩

/-- The quotient of the pendant edges is a forest. -/
theorem isAcyclic_blockQuotient_pendantEdges : (blockQuotient b (pendantEdges b E)).IsAcyclic :=
  ((isRelForest_iff (pendantEdges_le.trans hE)).1 (isRelForest_pendantEdges hE)).1

/-- Each edge of the quotient of the pendant edges comes from a single pendant edge. -/
theorem hasUniqueReps_pendantEdges : HasUniqueReps b (pendantEdges b E) :=
  ((isRelForest_iff (pendantEdges_le.trans hE)).1 (isRelForest_pendantEdges hE)).2

end Pendant

section Subpartition

variable {X : Finset (Finset ℕ)}

/-- **With an empty core, `G` is the only pendant tree**: `E ∈ 𝖳_0^X` (Definitions 5.25 (2),
5.26 (2), "if the core is empty, `G` is the only pendant tree"). -/
theorem isRelTree₀_of_twoCore_eq_empty (hX : IsSubpartition X) {E : SimpleGraph (X.biUnion id)}
    (hE : IsRelConnected₀ X E) (hcore : twoCore (blockOf hX) E = ∅) : IsRelTree₀ X E := by
  have hle := hE.le_interEdges
  have hcross : E ≤ crossBlockGraph (blockOf hX) := interEdges_eq hX ▸ hle
  have hpend : pendantEdges (blockOf hX) E = E := by
    ext u v
    rw [pendantEdges_adj, hcore]
    simp
  rw [isRelTree₀_iff hX]
  refine ⟨hle, ((isRelConnected₀_iff hX).1 hE).2, ?_⟩
  rw [intraEdges_eq hX, ← hpend]
  exact isRelForest_pendantEdges hcross

end Subpartition

end CoreForest

end MultipoleBKT

end
