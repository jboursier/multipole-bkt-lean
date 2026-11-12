/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.JGraphs
public import MultipoleBKT.LowerBound.AbsoluteLower.Components

/-!
# Flat tree structures for Lemmas 4.57–4.58

Lemma 4.57, and Lemma 4.58. After merging the even trees, the groups and their odd
trees form a flat structure. `flatHyp_of_relTree` gives the pair-set facts,
and `flat_structure` transfers them to graphs on `V_X` for integration.
-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open Finset SimpleGraph Multipole SetPartition SmallIntegral Hierarchical

variable {X : Finset (Finset ℕ)}

/-! ### Connectivity of pair sets -/

/-- Replacing the pairs `F` by pairs `G` that join their endpoints. -/
theorem connOn_union_replace {U : Finset ℕ} {E F G : Finset (ℕ × ℕ)} (h : ConnOn U (E ∪ F))
    (hF : ∀ p ∈ F, (edgeGraph (E ∪ G)).Reachable p.1 p.2) : ConnOn U (E ∪ G) := by
  refine ⟨h.1, fun i hi j hj => ?_⟩
  refine reachable_comp_of_forall_adj id (fun u w huw => ?_) (h.2 i hi j hj)
  rw [edgeGraph_adj] at huw
  obtain ⟨hne, huw | huw⟩ := huw
  · rcases mem_union.1 huw with h1 | h1
    · exact (edgeGraph_adj.2 ⟨hne, Or.inl (mem_union_left _ h1)⟩).reachable
    · exact hF _ h1
  · rcases mem_union.1 huw with h1 | h1
    · exact (edgeGraph_adj.2 ⟨hne, Or.inr (mem_union_left _ h1)⟩).reachable
    · exact (hF _ h1).symm

/-- Two points of a block of `X` are joined by the intra-block pairs of `X`. -/
theorem reachable_of_mem_block {E : Finset (ℕ × ℕ)} (hint : intraPairs X ⊆ E) {S : Finset ℕ}
    (hS : S ∈ X) {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S) : (edgeGraph E).Reachable a b := by
  rcases lt_trichotomy a b with h | rfl | h
  · refine (edgeGraph_adj.2 ⟨h.ne, Or.inl (hint ?_)⟩).reachable
    exact mem_intraPairs.2 ⟨S, hS, mem_pairsOn.2 ⟨ha, hb, h⟩⟩
  · exact Reachable.refl _
  · refine (edgeGraph_adj.2 ⟨h.ne', Or.inr (hint ?_)⟩).reachable
    exact mem_intraPairs.2 ⟨S, hS, mem_pairsOn.2 ⟨hb, ha, h⟩⟩

/-- The intra-block pairs of a subfamily are intra-block pairs. -/
theorem intraPairs_mono {Y : Finset (Finset ℕ)} (hYX : Y ⊆ X) : intraPairs Y ⊆ intraPairs X :=
  fun p hp => by
    obtain ⟨S, hS, hp⟩ := mem_intraPairs.1 hp
    exact mem_intraPairs.2 ⟨S, hYX hS, hp⟩

/-- The inter-block pairs of a subfamily of a subpartition are inter-block pairs. -/
theorem interPairs_mono (hX : IsSubpartition X) {Y : Finset (Finset ℕ)} (hYX : Y ⊆ X) :
    interPairs Y ⊆ interPairs X := by
  intro p hp
  obtain ⟨B, hB, B', hB', hBB', h1, h2⟩ := exists_of_mem_interPairs hp
  have hpY := mem_pairsOn.1 (interPairs_subset_pairsOn hp)
  rw [interPairs, mem_sdiff]
  refine ⟨mem_pairsOn.2 ⟨mem_biUnion.2 ⟨B, hYX hB, h1⟩, mem_biUnion.2 ⟨B', hYX hB', h2⟩,
    hpY.2.2⟩, fun hin => ?_⟩
  obtain ⟨S, hS, hpS⟩ := mem_intraPairs.1 hin
  have hpS' := mem_pairsOn.1 hpS
  have e1 : S = B := by
    by_contra h
    exact disjoint_left.1 (hX.2 hS (hYX hB) h) hpS'.1 h1
  have e2 : S = B' := by
    by_contra h
    exact disjoint_left.1 (hX.2 hS (hYX hB') h) hpS'.2.1 h2
  exact hBB' (e1.symm.trans e2)

/-- The pairs inside a group of blocks are intra-block pairs of a coarsening containing it. -/
theorem pairsOn_subset_intraPairs_coarsen {G : Finset (Finset (Finset ℕ))} {Y : Finset (Finset ℕ)}
    (hY : Y ∈ G) : pairsOn (Y.biUnion id) ⊆ intraPairs (coarsen X G) := fun _ hp =>
  mem_intraPairs.2 ⟨Y.biUnion id, mem_union_left _ (mem_image_of_mem _ hY), hp⟩

theorem connOn_mono' {U : Finset ℕ} {E F : Finset (ℕ × ℕ)} (h : ConnOn U E) (hEF : E ⊆ F) :
    ConnOn U F :=
  ⟨h.1, fun i hi j hj => (h.2 i hi j hj).mono (edgeGraph_mono hEF)⟩

/-- Intra- and inter-block pairs are distinct. -/
theorem disjoint_intraPairs_interPairs (Y : Finset (Finset ℕ)) {E E' : Finset (ℕ × ℕ)}
    (hE : E ⊆ intraPairs Y) (hE' : E' ⊆ interPairs Y) : Disjoint E E' :=
  disjoint_left.2 fun _ hp hp' => (mem_sdiff.1 (hE' hp')).2 (hE hp)

/-! ### Flat structures -/

/-- **A flat structure** on `X` (pairs): groups `G_k ⊆ X`, pairwise disjoint, odd trees
`T^a_k ⊆ ℰ^inter(G_k)` with `|T^a_k| + 1 = |G_k|`, even edges `E^b ⊆ ℰ^inter(X)` disjoint from the
odd trees, such that `⋃ T^a_k ∪ E^b ∪ ℰ^intra(X)` connects `V_X` with
`∑ |T^a_k| + |E^b| + 1 ≤ |X|`. The merged structures of Lemma 4.57 (groups `X_l`,
`T^a_l ∈ 𝖳^{X_l}`, `T^b ∈ 𝖳_0^{Coarse}`) are flat structures
by `flatHyp_of_relTree`. -/
structure FlatHyp {κ : Type*} [Fintype κ] (X : Finset (Finset ℕ)) (G : κ → Finset (Finset ℕ))
    (Ta : κ → Finset (ℕ × ℕ)) (Eb : Finset (ℕ × ℕ)) : Prop where
  subset : ∀ k, G k ⊆ X
  disj : ∀ k k', k ≠ k' → Disjoint (G k) (G k')
  inter : ∀ k, Ta k ⊆ interPairs (G k)
  card : ∀ k, (Ta k).card + 1 = (G k).card
  inter_b : Eb ⊆ interPairs X
  disj_ab : Disjoint (univ.biUnion Ta) Eb
  conn : ConnOn (X.biUnion id) ((univ.biUnion Ta ∪ Eb) ∪ intraPairs X)
  count : ∑ k, (Ta k).card + Eb.card + 1 ≤ X.card

section TwoLevel

variable {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)}

open scoped Classical in
/-- The two-level structures of Lemma 4.57 are flat structures. -/
theorem flatHyp_of_relTree (hX : IsSubpartition X) (hXsX : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l')) {Ta : Fin n → Finset (ℕ × ℕ)}
    (hTa : ∀ l, Ta l ∈ relTreePairs (Xs l)) {Tb : Finset (ℕ × ℕ)}
    (hTb : Tb ∈ relTreePairs₀ (coarsen X (univ.image Xs))) : FlatHyp X Xs Ta Tb := by
  have hG := relTree_group hX hXsX hTa
  obtain ⟨-, -, hGX, -, hTbi, hTbc, hTbcard, -⟩ := relTree_coarse hX hXsX hdisj hTa hTb
  refine ⟨hXsX, hdisj, fun l => (hG l).1, fun l => (hG l).2.2.1, ?_, ?_, ?_, ?_⟩
  · exact hTbi.trans (interPairs_coarsen_subset hGX)
  · refine (disjoint_biUnion_left _ _ _).2 fun l _ => disjoint_intraPairs_interPairs
      (coarsen X (univ.image Xs)) ?_ hTbi
    exact (hG l).1.trans (interPairs_subset_pairsOn.trans
      (pairsOn_subset_intraPairs_coarsen (mem_image_of_mem Xs (mem_univ l))))
  · have hstep : ConnOn (X.biUnion id) (Tb ∪ (univ.biUnion Ta ∪ intraPairs X)) := by
      refine connOn_union_replace hTbc fun p hp => ?_
      obtain ⟨B, hB, hpB⟩ := mem_intraPairs.1 hp
      have hpB' := mem_pairsOn.1 hpB
      rcases mem_union.1 hB with hB | hB
      · obtain ⟨Y, hY, rfl⟩ := mem_image.1 hB
        obtain ⟨l, -, rfl⟩ := mem_image.1 hY
        refine ((hG l).2.1.2 _ hpB'.1 _ hpB'.2.1).mono (edgeGraph_mono (union_subset ?_ ?_))
        · exact fun q hq => mem_union_right _ (mem_union_left _ (mem_biUnion.2 ⟨l, mem_univ _, hq⟩))
        · exact fun q hq => mem_union_right _ (mem_union_right _ (intraPairs_mono (hXsX l) hq))
      · exact reachable_of_mem_block (fun q hq => mem_union_right _ (mem_union_right _ hq))
          (mem_filter.1 hB).1 hpB'.1 hpB'.2.1
    refine connOn_mono' hstep ?_
    intro q hq
    rcases mem_union.1 hq with hq | hq
    · exact mem_union_left _ (mem_union_right _ hq)
    · rcases mem_union.1 hq with hq | hq
      · exact mem_union_left _ (mem_union_left _ hq)
      · exact mem_union_right _ hq
  · have hout : (coarsen X (univ.image Xs)).card + ∑ l, (Xs l).card ≤ n + X.card :=
      card_coarsen_add_le Xs hXsX hdisj
    have h3 : ∑ l, ((Ta l).card + 1) = ∑ l, (Xs l).card :=
      sum_congr rfl fun l _ => (hG l).2.2.1
    rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h3
    omega

end TwoLevel



/-! ### The flat structure on `V_X` -/

section Graph

open scoped Classical in
/-- **The hypotheses of `core_le_sum_tree`** on `V_X`, from a flat structure of pairs: groups
`G_k ⊆ X`, disjoint, with `T^a_k ⊆ ℰ^inter(G_k)`, `|T^a_k| + 1 = |G_k|`, even edges
`E^b ⊆ ℰ^inter(X)`, `⋃ T^a ∪ E^b ∪ ℰ^intra(X)` connecting `V_X`, and the count. -/
theorem flat_structure (hX : IsSubpartition X) {κ : Type*} [Fintype κ]
    (G : κ → Finset (Finset ℕ)) (hGX : ∀ k, G k ⊆ X)
    (hGd : ∀ k k', k ≠ k' → Disjoint (G k) (G k')) (Ta : κ → Finset (ℕ × ℕ))
    (hTa : ∀ k, Ta k ⊆ interPairs (G k)) (hTac : ∀ k, (Ta k).card + 1 = (G k).card)
    (Eb : Finset (ℕ × ℕ)) (hEb : Eb ⊆ interPairs X)
    (hconn : ConnOn (X.biUnion id) ((univ.biUnion Ta ∪ Eb) ∪ intraPairs X))
    (hcount : ∑ k, (Ta k).card + Eb.card + 1 ≤ X.card) :
    (∀ k k', k ≠ k' → Disjoint ((G k).subtype (· ∈ X)) ((G k').subtype (· ∈ X))) ∧
    (∀ k, ∀ e ∈ (graphOf (X.biUnion id) (Ta k)).edgeFinset, ∀ i ∈ e,
      Limits.blockOf X i ∈ (G k).subtype (· ∈ X)) ∧
    (∀ k, (graphOf (X.biUnion id) (Ta k)).edgeFinset.card + 1 = ((G k).subtype (· ∈ X)).card) ∧
    (∀ e ∈ univ.biUnion (fun k => (graphOf (X.biUnion id) (Ta k)).edgeFinset) ∪
      (graphOf (X.biUnion id) Eb).edgeFinset, ¬ (Sym2.map (Limits.blockOf X) e).IsDiag) ∧
    (∀ i j : X.biUnion id, (sameBlockGraph (Limits.blockOf X) ⊔
      fromEdgeSet ((univ.biUnion (fun k => (graphOf (X.biUnion id) (Ta k)).edgeFinset) ∪
        (graphOf (X.biUnion id) Eb).edgeFinset : Finset (Sym2 (X.biUnion id))) :
          Set (Sym2 (X.biUnion id)))).Reachable i j) ∧
    (∑ k, (graphOf (X.biUnion id) (Ta k)).edgeFinset.card +
      (graphOf (X.biUnion id) Eb).edgeFinset.card + 1 ≤ Fintype.card X) := by
  have hTaV : ∀ k, Ta k ⊆ pairsOn (X.biUnion id) := fun k =>
    ((hTa k).trans (interPairs_mono hX (hGX k))).trans interPairs_subset_pairsOn
  have hEbV : Eb ⊆ pairsOn (X.biUnion id) := hEb.trans interPairs_subset_pairsOn
  have hcardG : ∀ k, ((G k).subtype (· ∈ X)).card = (G k).card := fun k => by
    rw [card_subtype, filter_true_of_mem fun S hS => hGX k hS]
  -- inter-block pairs join distinct blocks
  have hinterX : ∀ (a b : X.biUnion id), (((a : ℕ), (b : ℕ)) ∈ interPairs X) →
      Limits.blockOf X a ≠ Limits.blockOf X b := by
    intro a b hab
    obtain ⟨B, hB, B', hB', hBB', h1, h2⟩ := exists_of_mem_interPairs hab
    rw [Limits.blockOf_eq hX hB h1, Limits.blockOf_eq hX hB' h2]
    exact fun h => hBB' (congrArg Subtype.val h)
  refine ⟨fun k k' hkk' => Finset.disjoint_left.2 fun S hS hS' =>
      Finset.disjoint_left.1 (hGd k k' hkk') (mem_subtype.1 hS) (mem_subtype.1 hS'), ?_, ?_, ?_,
      ?_, ?_⟩
  · -- the edges of `T^a_k` join blocks of `G_k`
    intro k e he i hi
    induction e using Sym2.ind with
    | h a b =>
      obtain ⟨-, hab | hab⟩ := mem_edgeFinset_graphOf_mk.1 he
      · have hp := mem_pairsOn.1 (interPairs_subset_pairsOn ((hTa k) hab))
        rcases Sym2.mem_iff.1 hi with rfl | rfl
        · exact blockOf_mem_subtype hX (hGX k) _ hp.1
        · exact blockOf_mem_subtype hX (hGX k) _ hp.2.1
      · have hp := mem_pairsOn.1 (interPairs_subset_pairsOn ((hTa k) hab))
        rcases Sym2.mem_iff.1 hi with rfl | rfl
        · exact blockOf_mem_subtype hX (hGX k) _ hp.2.1
        · exact blockOf_mem_subtype hX (hGX k) _ hp.1
  · intro k
    rw [card_edgeFinset_graphOf (hTaV k), hcardG]
    exact hTac k
  · intro e he
    induction e using Sym2.ind with
    | h a b =>
      rw [Sym2.map_mk, Sym2.mk_isDiag_iff]
      have hab' : ∀ E : Finset (ℕ × ℕ), E ⊆ interPairs X →
          s(a, b) ∈ (graphOf (X.biUnion id) E).edgeFinset →
            Limits.blockOf X a ≠ Limits.blockOf X b := by
        intro E hE hmem
        obtain ⟨-, h | h⟩ := mem_edgeFinset_graphOf_mk.1 hmem
        · exact hinterX a b (hE h)
        · exact fun h' => hinterX b a (hE h) h'.symm
      rcases mem_union.1 he with he | he
      · obtain ⟨k, -, he⟩ := mem_biUnion.1 he
        exact hab' (Ta k) ((hTa k).trans (interPairs_mono hX (hGX k))) he
      · exact hab' Eb hEb he
  · -- connectivity
    intro i j
    set H := sameBlockGraph (Limits.blockOf X) ⊔
      fromEdgeSet ((univ.biUnion (fun k => (graphOf (X.biUnion id) (Ta k)).edgeFinset) ∪
        (graphOf (X.biUnion id) Eb).edgeFinset : Finset (Sym2 (X.biUnion id))) :
          Set (Sym2 (X.biUnion id))) with hH
    have hsame : ∀ (B : Finset ℕ), B ∈ X → ∀ (a b : X.biUnion id), (a : ℕ) ∈ B → (b : ℕ) ∈ B →
        H.Reachable a b := by
      intro B hB a b ha hb
      by_cases hab : a = b
      · rw [hab]
      · refine Adj.reachable (sup_adj _ _ _ _ |>.2 (Or.inl (sameBlockGraph_adj.2 ⟨hab, ?_⟩)))
        rw [Limits.blockOf_eq hX hB ha, Limits.blockOf_eq hX hB hb]
    have hedge : ∀ (a b : X.biUnion id), (a : ℕ) ≠ b →
        s(a, b) ∈ univ.biUnion (fun k => (graphOf (X.biUnion id) (Ta k)).edgeFinset) ∪
          (graphOf (X.biUnion id) Eb).edgeFinset → H.Reachable a b := by
      intro a b hab hmem
      refine Adj.reachable (sup_adj _ _ _ _ |>.2 (Or.inr ?_))
      rw [fromEdgeSet_adj]
      exact ⟨mem_coe.2 hmem, fun h => hab (congrArg Subtype.val h)⟩
    refine reachable_of_connOn_lift H subset_rfl
      (union_subset (union_subset (biUnion_subset.2 fun k _ => hTaV k) hEbV)
        intraPairs_subset_pairsOn) ?_ hconn i.2 j.2
    intro p hp h1 h2
    rcases mem_union.1 hp with hp | hp
    · rcases mem_union.1 hp with hp | hp
      · obtain ⟨k, -, hp⟩ := mem_biUnion.1 hp
        have hlt := (mem_pairsOn.1 (hTaV k hp)).2.2
        exact hedge _ _ hlt.ne (mem_union_left _ (mem_biUnion.2 ⟨k, mem_univ _,
          mem_edgeFinset_graphOf_mk.2 ⟨hlt.ne, Or.inl hp⟩⟩))
      · have hlt := (mem_pairsOn.1 (hEbV hp)).2.2
        exact hedge _ _ hlt.ne (mem_union_right _ (mem_edgeFinset_graphOf_mk.2 ⟨hlt.ne, Or.inl hp⟩))
    · obtain ⟨B, hB, hpB⟩ := mem_intraPairs.1 hp
      have hpB' := mem_pairsOn.1 hpB
      exact hsame B hB _ _ hpB'.1 hpB'.2.1
  · -- the count
    have h1 : ∑ k, (graphOf (X.biUnion id) (Ta k)).edgeFinset.card = ∑ k, (Ta k).card :=
      sum_congr rfl fun k _ => card_edgeFinset_graphOf (hTaV k)
    rw [h1, card_edgeFinset_graphOf hEbV, Fintype.card_coe]
    exact hcount

end Graph

end AbsoluteLower

end MultipoleBKT

end
