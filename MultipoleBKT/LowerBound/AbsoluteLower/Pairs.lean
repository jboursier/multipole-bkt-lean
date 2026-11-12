/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Cluster.Penrose
public import MultipoleBKT.LowerBound.Hierarchical.ExpE11

/-!
# Relative graph notions as edge sets of pairs; the Penrose resummation for pairs

The activities of Section 4 (`MultipoleBKT.Hierarchical.modelActivity`, the reduction (4.61)
`MultipoleBKT.Hierarchical.coro_4_34`) write edge sets as finite sets of pairs `(i, j)`, `i < j`,
of labels (`MultipoleBKT.Multipole.EdgeSets`), while the Penrose resummation
(`MultipoleBKT.penrose`), the Eulerian notions (`MultipoleBKT.Parity.IsRelEulerian`) and the
peeling (`MultipoleBKT.Peeling`) are stated for simple graphs on `V_X = X.biUnion id`. The two are
related by the bijection `MultipoleBKT.Multipole.edgesOf` / `MultipoleBKT.Multipole.graphOf`.

Definitions 4.10 (Definition 4.10), 4.33
(Definition 4.33) and Lemma 4.51.

* `relTreePairs₀ X`, `relTreePairs X`: the trees `𝖳_0^X`, `𝖳^X` relative to `X` as edge sets of
  pairs (the edge sets of the graphs of `MultipoleBKT.relTrees₀`, `MultipoleBKT.relTrees`);
* `relEulerianConnectedPairs X`: `Eulc^X = 𝖤^X ∩ Eul^X` as edge sets of pairs;
* `relEdgeSets₀_eq_image`, `relEdgeSets_eq_image`: `𝖤_0^X` and `𝖤^X` (pairs) are the images of
  their graph versions;
* `edgesOf_interEdges`: `ℰ^inter(X)` (graphs) is `interPairs X`;
* `prod_edgesOf`: products over the pairs of a graph are products over its edges;
* `blockDeg_edgesOf`: the block degree of the pairs of a graph is its block degree, so that
  `isRelEulerianConnected_graphOf` transports `Eulc^X` to the graph version;
* **Penrose resummation for pairs** (Lemma 4.51): `sum_relEdgeSets₀_le` (nonnegative weights) and
  `abs_sum_relEdgeSets₀_le` (weights with `|1 + c_ij| ≤ 1`).
-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open Finset Multipole Hierarchical SetPartition

variable {X : Finset (Finset ℕ)}

/-! ### Edge sets of graphs on `V_X` -/

section Translate

/-- A graph on `V_X` has only inter-block edges iff its pairs lie in `ℰ^inter(X)`. -/
theorem le_interEdges_iff_edgesOf_subset (hX : IsSubpartition X)
    {G : SimpleGraph (X.biUnion id)} : G ≤ interEdges X ↔ edgesOf G ⊆ interPairs X := by
  rw [le_interEdges_iff]
  exact forall_adj_iff_edgesOf_subset_interPairs hX G

/-- `(V_X, G ∪ ℰ^intra(X))` is connected iff the pairs of `G` and `ℰ^intra(X)` connect `V_X`. -/
theorem connected_sup_intraEdges_iff_connOn {G : SimpleGraph (X.biUnion id)} :
    (G ⊔ intraEdges X).Connected ↔ ConnOn (X.biUnion id) (edgesOf G ∪ intraPairs X) :=
  connected_sup_iff G

/-- `ℰ^inter(X)` as a graph has the pairs `interPairs X`. -/
theorem edgesOf_interEdges (hX : IsSubpartition X) : edgesOf (interEdges X) = interPairs X := by
  refine subset_antisymm ((le_interEdges_iff_edgesOf_subset hX).1 le_rfl) fun p hp => ?_
  obtain ⟨B, hB, B', hB', hBB', h1, h2⟩ := exists_of_mem_interPairs hp
  have h12 := (mem_pairsOn.1 (interPairs_subset_pairsOn hp)).2.2
  refine mem_edgesOf.2 ⟨subset_biUnion_of_mem hB h1, subset_biUnion_of_mem hB' h2, h12, ?_⟩
  rw [interEdges, SimpleGraph.fromRel_adj]
  exact ⟨fun h => h12.ne (congrArg Subtype.val h), Or.inl ⟨B, hB, B', hB', hBB', h1, h2⟩⟩

/-- `G ∈ 𝖤_0^X` iff its pairs are in `𝖤_0^X`. -/
theorem isRelConnected₀_iff_mem (hX : IsSubpartition X) {G : SimpleGraph (X.biUnion id)} :
    IsRelConnected₀ X G ↔ edgesOf G ∈ relEdgeSets₀ X := by
  rw [isRelConnected₀_iff hX, mem_relEdgeSets₀, le_interEdges_iff_edgesOf_subset hX,
    connected_sup_intraEdges_iff_connOn]

/-- `G ∈ 𝖤^X` iff its pairs are in `𝖤^X`. -/
theorem isRelConnected_iff_mem (hX : IsSubpartition X) {G : SimpleGraph (X.biUnion id)} :
    IsRelConnected X G ↔ edgesOf G ∈ relEdgeSets X := by
  rw [IsRelConnected, mem_relEdgeSets, le_interEdges_iff_edgesOf_subset hX,
    connected_sup_intraEdges_iff_connOn, edgeSet_nonempty_iff, Finset.nonempty_iff_ne_empty]

theorem subset_pairsOn_of_mem_relEdgeSets₀ {E : Finset (ℕ × ℕ)} (hE : E ∈ relEdgeSets₀ X) :
    E ⊆ pairsOn (X.biUnion id) :=
  (mem_relEdgeSets₀.1 hE).1.trans interPairs_subset_pairsOn

/-- `𝖤_0^X` (pairs) is the image of `𝖤_0^X` (graphs). -/
theorem relEdgeSets₀_eq_image (hX : IsSubpartition X) :
    relEdgeSets₀ X = (relConnected₀ X).image edgesOf := by
  ext E
  rw [mem_image]
  constructor
  · intro hE
    refine ⟨graphOf _ E, ?_, edgesOf_graphOf (subset_pairsOn_of_mem_relEdgeSets₀ hE)⟩
    rw [mem_relConnected₀, isRelConnected₀_iff_mem hX,
      edgesOf_graphOf (subset_pairsOn_of_mem_relEdgeSets₀ hE)]
    exact hE
  · rintro ⟨G, hG, rfl⟩
    exact (isRelConnected₀_iff_mem hX).1 (mem_relConnected₀.1 hG)

/-- `𝖤^X` (pairs) is the image of `𝖤^X` (graphs). -/
theorem relEdgeSets_eq_image (hX : IsSubpartition X) :
    relEdgeSets X = (relConnected X).image edgesOf := by
  ext E
  rw [mem_image]
  constructor
  · intro hE
    have hsub := subset_pairsOn_of_mem_relEdgeSets₀ (relEdgeSets_subset_relEdgeSets₀ X hE)
    refine ⟨graphOf _ E, ?_, edgesOf_graphOf hsub⟩
    rw [mem_relConnected, isRelConnected_iff_mem hX, edgesOf_graphOf hsub]
    exact hE
  · rintro ⟨G, hG, rfl⟩
    exact (isRelConnected_iff_mem hX).1 (mem_relConnected.1 hG)

/-- The pairs of a graph on `V_X` are the sorted pairs of its edges. -/
theorem edgesOf_eq_image (G : SimpleGraph (X.biUnion id)) [Fintype G.edgeSet] :
    edgesOf G = G.edgeFinset.image fun e => ((e.inf : ℕ), (e.sup : ℕ)) := by
  ext p
  rw [mem_edgesOf, mem_image]
  constructor
  · rintro ⟨h1, h2, h12, hadj⟩
    refine ⟨s(⟨p.1, h1⟩, ⟨p.2, h2⟩), SimpleGraph.mem_edgeFinset.2 hadj, ?_⟩
    have hle : (⟨p.1, h1⟩ : X.biUnion id) ≤ ⟨p.2, h2⟩ := h12.le
    simp only [Sym2.inf_mk, Sym2.sup_mk, inf_of_le_left hle, sup_of_le_right hle]
  · rintro ⟨e, he, rfl⟩
    induction e using Sym2.ind with
    | h a b =>
      have hab := SimpleGraph.mem_edgeFinset.1 he
      rw [SimpleGraph.mem_edgeSet] at hab
      rcases lt_or_gt_of_ne hab.ne with h | h
      · simp only [Sym2.inf_mk, Sym2.sup_mk, inf_of_le_left h.le, sup_of_le_right h.le]
        exact ⟨a.2, b.2, h, hab⟩
      · simp only [Sym2.inf_mk, Sym2.sup_mk, inf_of_le_right h.le, sup_of_le_left h.le]
        exact ⟨b.2, a.2, h, hab.symm⟩

theorem injOn_sortedPair (s : Finset (Sym2 (X.biUnion id))) :
    Set.InjOn (fun e : Sym2 (X.biUnion id) => ((e.inf : ℕ), (e.sup : ℕ))) s := by
  intro e _ e' _ h
  simp only [Prod.mk.injEq] at h
  exact Sym2.inf_eq_inf_and_sup_eq_sup.1 ⟨Subtype.ext h.1, Subtype.ext h.2⟩

/-- Products over the pairs of a graph are products over its edges. -/
theorem prod_edgesOf {M : Type*} [CommMonoid M] (G : SimpleGraph (X.biUnion id))
    [Fintype G.edgeSet] (w : ℕ × ℕ → M) :
    ∏ p ∈ edgesOf G, w p = ∏ e ∈ G.edgeFinset, w ((e.inf : ℕ), (e.sup : ℕ)) := by
  rw [edgesOf_eq_image, prod_image (injOn_sortedPair _)]

theorem card_edgesOf (G : SimpleGraph (X.biUnion id)) [Fintype G.edgeSet] :
    (edgesOf G).card = G.edgeFinset.card := by
  rw [edgesOf_eq_image, card_image_of_injOn (injOn_sortedPair _)]

end Translate

/-! ### Relative trees and connected Eulerian edge sets as pairs -/

section Trees

open scoped Classical

variable (X) in
/-- `𝖳_0^X` (Definition 4.10(6)) as edge sets of pairs: the pairs of the trees
relative to `X` (`MultipoleBKT.relTrees₀`). -/
noncomputable def relTreePairs₀ : Finset (Finset (ℕ × ℕ)) :=
  (relTrees₀ X).image edgesOf

variable (X) in
/-- `𝖳^X` (Definition 4.10(5)) as edge sets of pairs. -/
noncomputable def relTreePairs : Finset (Finset (ℕ × ℕ)) :=
  (relTrees X).image edgesOf

variable (X) in
/-- `Eulc^X = 𝖤^X ∩ Eul^X` (Definition 4.33) as edge sets of pairs. -/
noncomputable def relEulerianConnectedPairs : Finset (Finset (ℕ × ℕ)) :=
  relEdgeSets X ∩ relEulerianPairs X

theorem mem_relEulerianConnectedPairs {E : Finset (ℕ × ℕ)} :
    E ∈ relEulerianConnectedPairs X ↔ E ∈ relEdgeSets X ∧ E ∈ relEulerianPairs X :=
  mem_inter

/-- A relative tree has `|X| - 1` pairs. -/
theorem card_add_one_of_mem_relTreePairs₀ (hX : IsSubpartition X) {T : Finset (ℕ × ℕ)}
    (hT : T ∈ relTreePairs₀ X) : T.card + 1 = X.card := by
  obtain ⟨G, hG, rfl⟩ := mem_image.1 hT
  rw [card_edgesOf]
  exact (mem_relTrees₀.1 hG).card_edgeFinset hX

theorem subset_interPairs_of_mem_relTreePairs₀ (hX : IsSubpartition X) {T : Finset (ℕ × ℕ)}
    (hT : T ∈ relTreePairs₀ X) : T ⊆ interPairs X := by
  obtain ⟨G, hG, rfl⟩ := mem_image.1 hT
  exact (le_interEdges_iff_edgesOf_subset hX).1 (mem_relTrees₀.1 hG).le_interEdges

theorem subset_interPairs_of_mem_relTreePairs (hX : IsSubpartition X) {T : Finset (ℕ × ℕ)}
    (hT : T ∈ relTreePairs X) : T ⊆ interPairs X := by
  obtain ⟨G, hG, rfl⟩ := mem_image.1 hT
  exact (le_interEdges_iff_edgesOf_subset hX).1 (mem_relTrees.1 hG).1.le_interEdges

/-- A relative tree has at most `|V_X|` pairs. -/
theorem card_le_of_mem_relTreePairs₀ (hX : IsSubpartition X) {T : Finset (ℕ × ℕ)}
    (hT : T ∈ relTreePairs₀ X) : T.card ≤ (X.biUnion id).card := by
  have h1 := card_add_one_of_mem_relTreePairs₀ hX hT
  have h2 : X.card ≤ (X.biUnion id).card :=
    card_le_card_biUnion (fun S hS S' hS' hne => hX.2 hS hS' hne) hX.1
  omega

end Trees

/-! ### Block degrees and Eulerian edge sets -/

section Eulerian

open scoped Classical

/-- The block degree of the pairs of a graph is its block degree:
`deg_{edgesOf G}(S) = ∑_{i ∈ S} deg_G(i)` (Definition 4.10(7)). -/
theorem blockDeg_edgesOf (G : SimpleGraph (X.biUnion id)) (S : Finset ℕ) :
    blockDeg (edgesOf G) S = blockDegree X G S := by
  set B : Finset (X.biUnion id) := S.subtype (· ∈ X.biUnion id) with hB
  have hdeg : blockDegree X G S = ((B ×ˢ univ).filter fun q => G.Adj q.1 q.2).card := by
    rw [blockDegree, ← hB, card_filter, sum_product]
    refine sum_congr rfl fun i _ => ?_
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter, card_filter]
  rw [hdeg, ← card_filter_add_card_filter_not (p := fun q => q.1 < q.2), filter_filter,
    filter_filter, blockDeg]
  congr 1
  · refine card_bij' (fun p hp => (⟨p.1, ?_⟩, ⟨p.2, ?_⟩)) (fun q _ => ((q.1 : ℕ), (q.2 : ℕ)))
      ?_ ?_ ?_ ?_
    · exact (mem_edgesOf.1 (mem_filter.1 hp).1).1
    · exact (mem_edgesOf.1 (mem_filter.1 hp).1).2.1
    · intro p hp
      obtain ⟨hpE, hpS⟩ := mem_filter.1 hp
      obtain ⟨h1, h2, h12, hadj⟩ := mem_edgesOf.1 hpE
      simp only [mem_filter, mem_product, mem_univ, and_true, hB, mem_subtype]
      exact ⟨hpS, hadj, h12⟩
    · intro q hq
      simp only [mem_filter, mem_product, mem_univ, and_true, hB, mem_subtype] at hq
      exact mem_filter.2 ⟨mem_edgesOf.2 ⟨q.1.2, q.2.2, hq.2.2, hq.2.1⟩, hq.1⟩
    · intro p hp
      rfl
    · intro q hq
      rfl
  · refine card_bij' (fun p hp => (⟨p.2, ?_⟩, ⟨p.1, ?_⟩)) (fun q _ => ((q.2 : ℕ), (q.1 : ℕ)))
      ?_ ?_ ?_ ?_
    · exact (mem_edgesOf.1 (mem_filter.1 hp).1).2.1
    · exact (mem_edgesOf.1 (mem_filter.1 hp).1).1
    · intro p hp
      obtain ⟨hpE, hpS⟩ := mem_filter.1 hp
      obtain ⟨h1, h2, h12, hadj⟩ := mem_edgesOf.1 hpE
      simp only [mem_filter, mem_product, mem_univ, and_true, hB, mem_subtype, not_lt]
      exact ⟨hpS, hadj.symm, h12.le⟩
    · intro q hq
      simp only [mem_filter, mem_product, mem_univ, and_true, hB, mem_subtype, not_lt] at hq
      exact mem_filter.2 ⟨mem_edgesOf.2 ⟨q.2.2, q.1.2,
        lt_of_le_of_ne hq.2.2 (fun h => hq.2.1.ne (Subtype.ext h).symm), hq.2.1.symm⟩, hq.1⟩
    · intro p hp
      rfl
    · intro q hq
      rfl

/-- The graph of an Eulerian edge set of pairs is Eulerian relative to `X`. -/
theorem isRelEulerian_graphOf (hX : IsSubpartition X) {E : Finset (ℕ × ℕ)}
    (hE : E ∈ relEulerianPairs X) : Parity.IsRelEulerian X (graphOf _ E) := by
  rw [mem_relEulerianPairs] at hE
  have hsub : E ⊆ pairsOn (X.biUnion id) := hE.1.trans interPairs_subset_pairsOn
  refine ⟨(le_interEdges_iff_edgesOf_subset hX).2 ((edgesOf_graphOf hsub).symm ▸ hE.1),
    fun S hS => ?_⟩
  rw [← blockDeg_edgesOf, edgesOf_graphOf hsub]
  exact hE.2 S hS

/-- The graph of an edge set of `Eulc^X` (pairs) is in `Eulc^X` (graphs). -/
theorem isRelEulerianConnected_graphOf (hX : IsSubpartition X) {E : Finset (ℕ × ℕ)}
    (hE : E ∈ relEulerianConnectedPairs X) :
    Parity.IsRelEulerianConnected X (graphOf _ E) := by
  rw [mem_relEulerianConnectedPairs] at hE
  have hsub : E ⊆ pairsOn (X.biUnion id) :=
    subset_pairsOn_of_mem_relEdgeSets₀ (relEdgeSets_subset_relEdgeSets₀ X hE.1)
  refine ⟨?_, isRelEulerian_graphOf hX hE.2⟩
  rw [isRelConnected_iff_mem hX, edgesOf_graphOf hsub]
  exact hE.1

end Eulerian

/-! ### The Penrose resummation for edge sets of pairs -/

section Penrose

open scoped Classical

/-- Sums over `𝖤_0^X` of products over pairs are sums over the graphs of `𝖤_0^X`. -/
theorem sum_relEdgeSets₀_eq (hX : IsSubpartition X) {R : Type*} [CommSemiring R]
    (w : ℕ × ℕ → R) :
    ∑ E ∈ relEdgeSets₀ X, ∏ p ∈ E, w p =
      ∑ H ∈ relConnected₀ X, ∏ e ∈ H.edgeFinset, w ((e.inf : ℕ), (e.sup : ℕ)) := by
  rw [relEdgeSets₀_eq_image hX, sum_image fun G _ G' _ h => edgesOf_injective h]
  exact sum_congr rfl fun H _ => prod_edgesOf H w

theorem sum_relTreePairs₀_eq {R : Type*} [AddCommMonoid R] (f : Finset (ℕ × ℕ) → R) :
    ∑ T ∈ relTreePairs₀ X, f T = ∑ T ∈ relTrees₀ X, f (edgesOf T) := by
  rw [relTreePairs₀, sum_image fun G _ G' _ h => edgesOf_injective h]

theorem sum_relTreePairs_eq {R : Type*} [AddCommMonoid R] (f : Finset (ℕ × ℕ) → R) :
    ∑ T ∈ relTreePairs X, f T = ∑ T ∈ relTrees X, f (edgesOf T) := by
  rw [relTreePairs, sum_image fun G _ G' _ h => edgesOf_injective h]

/-- **Penrose resummation for nonnegative weights** (Lemma 4.51 as used in Step 1 of proof of Lemma 4.54), for edge sets of pairs: if `w ≥ 0` on `ℰ^inter(X)`, then
`∑_{H ∈ 𝖤_0^X} ∏_{ij ∈ H} w_ij ≤ ∑_{T ∈ 𝖳_0^X} ∏_{ij ∈ T} w_ij ∏_{ij ∈ ℰ^inter(X)} (1 + w_ij)`. -/
theorem sum_relEdgeSets₀_le (hX : IsSubpartition X) (w : ℕ × ℕ → ℝ)
    (hw : ∀ p ∈ interPairs X, 0 ≤ w p) :
    ∑ E ∈ relEdgeSets₀ X, ∏ p ∈ E, w p ≤
      ∑ T ∈ relTreePairs₀ X, (∏ p ∈ T, w p) * ∏ p ∈ interPairs X, (1 + w p) := by
  rw [sum_relEdgeSets₀_eq hX, sum_relTreePairs₀_eq, ← edgesOf_interEdges hX]
  have hc : ∀ e ∈ (interEdges X).edgeSet, 0 ≤ w ((e.inf : ℕ), (e.sup : ℕ)) := by
    intro e he
    refine hw _ ?_
    rw [← edgesOf_interEdges hX, edgesOf_eq_image]
    exact mem_image_of_mem _ (SimpleGraph.mem_edgeFinset.2 he)
  refine (penrose_le hX (fun e => w ((e.inf : ℕ), (e.sup : ℕ))) hc).trans_eq ?_
  refine sum_congr rfl fun T _ => ?_
  rw [prod_edgesOf, prod_edgesOf]

/-- **Penrose resummation for weights with `|1 + w| ≤ 1`** (Lemma 4.51 as used in Step 2 of
Lemma 4.54 with `w = -𝟙_𝓑`, equation (4.93) in the proof of Lemma 4.54), for edge sets of pairs:
`|∑_{H ∈ 𝖤_0^X} ∏_{ij ∈ H} w_ij| ≤ ∑_{T ∈ 𝖳_0^X} ∏_{ij ∈ T} |w_ij|`. -/
theorem abs_sum_relEdgeSets₀_le (hX : IsSubpartition X) (w : ℕ × ℕ → ℝ)
    (hw : ∀ p ∈ interPairs X, |1 + w p| ≤ 1) :
    |∑ E ∈ relEdgeSets₀ X, ∏ p ∈ E, w p| ≤ ∑ T ∈ relTreePairs₀ X, ∏ p ∈ T, |w p| := by
  rw [sum_relEdgeSets₀_eq hX, sum_relTreePairs₀_eq]
  have hc : ∀ e ∈ (interEdges X).edgeSet, |1 + w ((e.inf : ℕ), (e.sup : ℕ))| ≤ 1 := by
    intro e he
    refine hw _ ?_
    rw [← edgesOf_interEdges hX, edgesOf_eq_image]
    exact mem_image_of_mem _ (SimpleGraph.mem_edgeFinset.2 he)
  refine (abs_penrose_le hX (fun e => w ((e.inf : ℕ), (e.sup : ℕ))) hc).trans_eq ?_
  refine sum_congr rfl fun T _ => ?_
  rw [prod_edgesOf]

end Penrose

end AbsoluteLower

end MultipoleBKT

end
