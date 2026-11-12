/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Quadratic.MinimalSkeleton
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# The edges of a minimal skeleton and `𝒯_+^X ∈ 𝖳^X`

The paper: Definition 5.29 and
the proof of Corollary 5.34. For a minimal skeleton `E` (relative to the blocks of
`b`) with `E ∪ ℰ^intra` connected, and an admissible peeling `(Ts, Fs)` of its bridge-blocks
(`MultipoleBKT.CoreForest.IsPlusPeeling`):

* `eq_iSup_sup_relBridges`: `E = ⋃_l G_l ∪ ℰ_br(E)`, where `G_l` are the bridge-blocks of the
  2-core and `ℰ_br(E)` the bridges of the full quotient (`relBridges b E`);
* `plusTree_eq`: `𝒯_+^X = ⋃_l 𝒯^{X_l} ∪ ℰ_br(E)`;
* `prod_edgeFinset_eq`, `prod_edgeFinset_plusTree_eq`: the corresponding products over edges;
* `natCard_edgeSet_blockInnerEdges_le`: `|E(G_l)| ≤ 2 |V(G_l)|` (a minimally 2-edge-connected graph
  has at most `2(|X_l| - 1)` edges, Corollary 4.47);
* `card_edgeFinset_tree_add_one`: `|𝒯^{X_l}| + 1 = |X_l|`;
* `isRelTree_plusTree`: **`𝒯_+^X ∈ 𝖳^X`** (claimed without proof after Definition 5.29).
-/

@[expose] public section

open Finset SimpleGraph

namespace MultipoleBKT

namespace UpperBound

namespace Quadratic

open CoreForest Peeling

/-! ### Products over the edges of a union -/

section Union

variable {V : Type*} [Fintype V]

open scoped Classical in
theorem disjoint_edgeFinset_of_disjoint {G H : SimpleGraph V} (h : Disjoint G H) :
    Disjoint G.edgeFinset H.edgeFinset := by
  rw [Finset.disjoint_left]
  intro e hG hH
  induction e using Sym2.ind with
  | h u v =>
    rw [mem_edgeFinset, mem_edgeSet] at hG hH
    have : (G ⊓ H).Adj u v := ⟨hG, hH⟩
    rw [disjoint_iff.1 h] at this
    exact this

open scoped Classical in
/-- Products over the edges of `(⨆ i, G i) ⊔ H` for pairwise disjoint `G i`, disjoint from `H`. -/
theorem prod_edgeFinset_iSup_sup [DecidableEq V] {ι : Type*} [Fintype ι] {G : ι → SimpleGraph V}
    {H : SimpleGraph V} (hG : ∀ i j, i ≠ j → Disjoint (G i) (G j))
    (hGH : ∀ i, Disjoint (G i) H) {M : Type*} [CommMonoid M] (f : Sym2 V → M) :
    ∏ e ∈ ((⨆ i, G i) ⊔ H).edgeFinset, f e =
      (∏ i, ∏ e ∈ (G i).edgeFinset, f e) * ∏ e ∈ H.edgeFinset, f e := by
  have hset : ((⨆ i, G i) ⊔ H).edgeFinset =
      (univ.biUnion fun i => (G i).edgeFinset) ∪ H.edgeFinset := by
    ext e
    simp only [mem_edgeFinset, edgeSet_sup, edgeSet_iSup, Set.mem_union, Set.mem_iUnion,
      Finset.mem_union, Finset.mem_biUnion, mem_univ, true_and]
  rw [hset, Finset.prod_union, Finset.prod_biUnion]
  · intro i _ j _ hij
    exact disjoint_edgeFinset_of_disjoint (hG i j hij)
  · rw [Finset.disjoint_biUnion_left]
    exact fun i _ => disjoint_edgeFinset_of_disjoint (hGH i)

omit [Fintype V] in
/-- The number of edges of a graph read back from a set of vertices. -/
theorem natCard_edgeSet_map {W : Type*} (f : W ↪ V) (H : SimpleGraph W) :
    Nat.card (H.map f).edgeSet = Nat.card H.edgeSet := by
  rw [edgeSet_map]
  exact Nat.card_image_of_injective (Sym2.map.injective f.injective) _

end Union

/-! ### The edges of a minimal skeleton -/

section Skeleton

variable {V β : Type*} [Fintype V] [Fintype β] [DecidableEq β] {b : V → β}
  {E : SimpleGraph V}

theorem blockInnerEdges_le (l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent) :
    blockInnerEdges b E l ≤ E :=
  fun _ _ h => coreEdges_le (blockInnerEdges_adj.1 h).1

theorem blockInnerEdges_adj_inBlock
    {l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent} {u v : V}
    (h : (blockInnerEdges b E l).Adj u v) :
    bridgeBlock b (coreEdges b E) u = l ∧ bridgeBlock b (coreEdges b E) v = l := by
  obtain ⟨hc, hnb, hu⟩ := blockInnerEdges_adj.1 h
  exact ⟨hu, (bridgeBlock_eq_of_adj_of_not_relBridges hc hnb).symm.trans hu⟩

theorem disjoint_blockInnerEdges {l l' : (bridgelessGraph b (coreEdges b E)).ConnectedComponent}
    (hne : l ≠ l') : Disjoint (blockInnerEdges b E l) (blockInnerEdges b E l') := by
  rw [disjoint_iff]
  ext u v
  simp only [inf_adj, bot_adj, iff_false, not_and]
  intro h h'
  exact hne ((blockInnerEdges_adj_inBlock h).1.symm.trans (blockInnerEdges_adj_inBlock h').1)

variable (hE : E ≤ crossBlockGraph b)
include hE

theorem disjoint_blockInnerEdges_relBridges
    (l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent) :
    Disjoint (blockInnerEdges b E l) (relBridges b E) := by
  rw [disjoint_iff]
  ext u v
  simp only [inf_adj, bot_adj, iff_false, not_and]
  intro h hb
  obtain ⟨hc, hnb, -⟩ := blockInnerEdges_adj.1 h
  rw [relBridges_eq_sup hE] at hb
  rcases hb with hp | hb
  · rw [pendantEdges, sdiff_adj] at hp
    exact hp.2 hc
  · exact hnb hb

/-- For a minimal skeleton, `E = ⋃_l G_l ∪ ℰ_br(E)`. -/
theorem eq_iSup_sup_relBridges (hEE : IsMinimalSkeleton b E E) :
    E = (⨆ l, blockInnerEdges b E l) ⊔ relBridges b E := by
  have hself := (isMinimalSkeleton_self_iff.1 hEE)
  obtain ⟨Ks, hKs, hEq⟩ := hEE
  have hKl : ∀ l, Ks l = blockInnerEdges b E l := by
    intro l
    refine le_antisymm (hKs l).1 fun u v huv => ?_
    obtain ⟨hc, hnb, hu⟩ := blockInnerEdges_adj.1 huv
    have huvE : E.Adj u v := coreEdges_le hc
    rw [hEq] at huvE
    rcases huvE with (h | h) | h
    · obtain ⟨l', hl'⟩ := (iSup_adj).1 h
      have hu' := (blockInnerEdges_adj.1 ((hKs l').1 hl')).2.2
      rw [hu'] at hu
      exact hu ▸ hl'
    · exact absurd (pendantEdges_adj.1 h).2
        (by rw [coreEdges_adj] at hc; push Not; exact ⟨hc.2.1, hc.2.2⟩)
    · exact absurd h hnb
  have hKs' : Ks = fun l => blockInnerEdges b E l := funext hKl
  conv_lhs => rw [hEq, hKs']
  rw [relBridges_eq_sup hE, sup_assoc]

/-- `𝒯_+^X = ⋃_l 𝒯^{X_l} ∪ ℰ_br(E)` (the bridges of the full quotient are the pendant edges and the
bridges of the core). -/
theorem plusTree_eq (Ts : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → SimpleGraph V) :
    plusTree b E Ts = (⨆ l, Ts l) ⊔ relBridges b E := by
  rw [plusTree, relBridges_eq_sup hE, sup_assoc]

omit [Fintype β] [DecidableEq β] in
/-- The bridges of the full quotient form a tree on its bridge-blocks. -/
theorem natCard_relBridges_add_one (hconn : (E ⊔ sameBlockGraph b).Connected) :
    Nat.card (relBridges b E).edgeSet + 1 =
      Nat.card (bridgelessGraph b E).ConnectedComponent := by
  classical
  have h1 := natCard_edgeSet_eq_of_hasUniqueReps (relBridges_le_crossBlockGraph hE)
    (hasUniqueReps_relBridges hE)
  have h2 := (bridgeTree_isTree hE hconn).card_edgeFinset
  rw [edgeFinset_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h2
  rw [h1]
  exact h2

end Skeleton

/-! ### The peeling of the bridge-blocks -/

section Peeling

variable {V β : Type*} [Fintype V] [Fintype β] [DecidableEq β] {b : V → β}
  {E : SimpleGraph V} {r : V → ℝ} {d : Sym2 V → ℝ}
  {v₁ : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → V}
  {e₀ : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → Sym2 V}
  {Ts Fs : (bridgelessGraph b (coreEdges b E)).ConnectedComponent → SimpleGraph V}

open scoped Classical in
theorem card_partsOn_eq (l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent) :
    Fintype.card (PartsOn b (InBlock b E l)) = (blockParts b E l).card := by
  classical
  rw [Fintype.card_subtype]
  congr 1
  ext S
  rw [Finset.mem_filter, mem_blockParts]
  exact ⟨fun ⟨_, w, hw⟩ => ⟨w.1, w.2, hw⟩, fun ⟨v, hv, hvS⟩ => ⟨Finset.mem_univ _, ⟨v, hv⟩, hvS⟩⟩

open scoped Classical in
theorem card_blockParts_le (l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent) :
    (blockParts b E l).card ≤ (univ.filter fun v => bridgeBlock b (coreEdges b E) v = l).card := by
  rw [← card_partsOn_eq, ← Fintype.card_subtype]
  exact Fintype.card_le_of_surjective _ blockOn_surjective

variable (hE : E ≤ crossBlockGraph b) (hEE : IsMinimalSkeleton b E E)
  (hP : IsPlusPeeling b E (blockInnerEdges b E) r d v₁ e₀ Ts Fs)
include hE hEE hP

theorem tree_sup_removed (l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent) :
    Ts l ⊔ Fs l = blockInnerEdges b E l ∧ Disjoint (Ts l) (Fs l) := by
  have hK := (isMinimalSkeleton_self_iff.1 hEE) l
  by_cases h1 : (blockParts b E l).card = 1
  · obtain ⟨hT, hF⟩ := (hP l).2 h1
    rw [hT, hF, sup_bot_eq, blockInnerEdges_eq_bot_of_card_eq_one hE h1]
    exact ⟨rfl, disjoint_bot_left⟩
  · have h := (hP l).1 h1
    exact ⟨h.sup_eq hK, h.disjoint⟩

open scoped Classical in
/-- `|E(G_l)| ≤ 2 |V(G_l)|`: a bridge-block is minimally 2-edge-connected relative to its parts, so
it has at most `2(|X_l| - 1)` edges (the edge count of Corollary 4.47). -/
theorem natCard_edgeSet_blockInnerEdges_le
    (l : (bridgelessGraph b (coreEdges b E)).ConnectedComponent) :
    Nat.card (blockInnerEdges b E l).edgeSet ≤
      2 * (univ.filter fun v => bridgeBlock b (coreEdges b E) v = l).card := by
  by_cases h1 : (blockParts b E l).card = 1
  · rw [blockInnerEdges_eq_bot_of_card_eq_one hE h1, edgeSet_bot]
    simp
  · obtain ⟨w₁, e₀', Qs, hp, -, -, -, -⟩ := (hP l).1 h1
    have hK := (isMinimalSkeleton_self_iff.1 hEE) l
    have hKeq : blockInnerEdges b E l = ((blockInnerEdges b E l).comap Subtype.val).map
        (Function.Embedding.subtype (InBlock b E l)) :=
      (map_comap_eq fun u v h => hK.adj_inBlock h).symm
    have hc := hp.decomp.natCard_edgeSet_le
    have hpart : Fintype.card (PartsOn b (InBlock b E l)) ≤
        Fintype.card {v // InBlock b E l v} :=
      Fintype.card_le_of_surjective _ blockOn_surjective
    rw [hKeq, natCard_edgeSet_map]
    calc Nat.card ((blockInnerEdges b E l).comap Subtype.val).edgeSet
        ≤ 2 * (Fintype.card (PartsOn b (InBlock b E l)) - 1) := hc
      _ ≤ 2 * Fintype.card {v // InBlock b E l v} := by omega
      _ = 2 * (univ.filter fun v => bridgeBlock b (coreEdges b E) v = l).card := by
          rw [Fintype.card_subtype]

end Peeling

end Quadratic

end UpperBound

end MultipoleBKT

end
