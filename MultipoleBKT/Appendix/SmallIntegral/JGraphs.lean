/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.JCore
public import MultipoleBKT.LowerBound.BoundedLowerEps.Transfer

/-!
# The trees of Lemma A.4 as edge sets on `V_X`

See Lemma A.4. For a
subpartition `X`, disjoint groups `X_1, …, X_n ⊆ X`, trees `T^a_l ∈ 𝖳^{X_l}` relative to the groups
and a tree `T^b ∈ 𝖳_0^{Coarse_X(X_1, …, X_n)}` relative to the coarsening (all given as edge sets of
pairs, `edgesOf` of the graphs of `MultipoleBKT.relTrees`), the edge sets `T^a_l`, `T^b` read on
`V_X` satisfy the structural hypotheses of the retained-tree construction
(`trees_structure`): the groups of blocks are disjoint, the edges of `T^a_l` join blocks of `X_l`,
`|T^a_l| + 1 = |X_l|`, every edge joins distinct blocks of `X`, the blocks together with
`T^a ∪ T^b` connect `V_X`, and `∑_l |T^a_l| + |T^b| + 1 ≤ |X|`.
-/

@[expose] public section

namespace MultipoleBKT

namespace SmallIntegral

open Finset SimpleGraph
open Multipole SetPartition Limits Hierarchical BoundedLowerEps

/-! ### Edge sets and graphs -/

section Graphs

variable {U : Finset ℕ}

open scoped Classical in
theorem card_edgesOf (G : SimpleGraph U) : (edgesOf G).card = G.edgeFinset.card := by
  refine card_bij (fun p hp => s(⟨p.1, (mem_edgesOf.1 hp).1⟩, ⟨p.2, (mem_edgesOf.1 hp).2.1⟩))
    ?_ ?_ ?_
  · intro p hp
    obtain ⟨h1, h2, -, hadj⟩ := mem_edgesOf.1 hp
    rw [mem_edgeFinset, mem_edgeSet]
    exact hadj
  · intro p hp q hq h
    obtain ⟨-, -, hp12, -⟩ := mem_edgesOf.1 hp
    obtain ⟨-, -, hq12, -⟩ := mem_edgesOf.1 hq
    rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext (congrArg Subtype.val h1) (congrArg Subtype.val h2)
    · have a := congrArg Subtype.val h1
      have b := congrArg Subtype.val h2
      simp only at a b
      omega
  · intro e he
    induction e using Sym2.ind with
    | h i j =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      rcases lt_or_gt_of_ne (fun h : (i : ℕ) = j => he.ne (Subtype.ext h)) with hlt | hlt
      · exact ⟨((i : ℕ), (j : ℕ)), mem_edgesOf.2 ⟨i.2, j.2, hlt, he⟩, rfl⟩
      · exact ⟨((j : ℕ), (i : ℕ)), mem_edgesOf.2 ⟨j.2, i.2, hlt, he.symm⟩, Sym2.eq_swap⟩

open scoped Classical in
theorem card_edgeFinset_graphOf {E : Finset (ℕ × ℕ)} (hE : E ⊆ pairsOn U) :
    (graphOf U E).edgeFinset.card = E.card := by
  rw [← card_edgesOf, edgesOf_graphOf hE]

/-- **Lifting connectivity**: if `E ⊆ pairsOn U` connects `U` and each pair of `E` is joined in a
graph `H` on `V ⊇ U`, then `H` joins any two points of `U`. -/
theorem reachable_of_connOn_lift {V : Finset ℕ} (H : SimpleGraph V) (hUV : U ⊆ V)
    {E : Finset (ℕ × ℕ)} (hE : E ⊆ pairsOn U)
    (hEH : ∀ p ∈ E, ∀ (h1 : p.1 ∈ V) (h2 : p.2 ∈ V), H.Reachable ⟨p.1, h1⟩ ⟨p.2, h2⟩)
    (hc : ConnOn U E) {i j : V} (hi : (i : ℕ) ∈ U) (hj : (j : ℕ) ∈ U) : H.Reachable i j := by
  have key : ∀ (a b : ℕ) (P : (edgeGraph E).Walk a b) (ha : a ∈ U),
      ∃ hb : b ∈ U, H.Reachable ⟨a, hUV ha⟩ ⟨b, hUV hb⟩ := by
    intro a b P
    induction P with
    | nil => exact fun ha => ⟨ha, Reachable.refl _⟩
    | @cons a c b hadj P ih =>
      intro ha
      rw [edgeGraph_adj] at hadj
      obtain ⟨-, hp | hp⟩ := hadj
      · have hc' : c ∈ U := (mem_pairsOn.1 (hE hp)).2.1
        obtain ⟨hb, hr⟩ := ih hc'
        exact ⟨hb, (hEH _ hp (hUV ha) (hUV hc')).trans hr⟩
      · have hc' : c ∈ U := (mem_pairsOn.1 (hE hp)).1
        obtain ⟨hb, hr⟩ := ih hc'
        exact ⟨hb, (hEH _ hp (hUV hc') (hUV ha)).symm.trans hr⟩
  obtain ⟨P⟩ := hc.2 i hi j hj
  obtain ⟨_, hr⟩ := key i j P hi
  exact hr

end Graphs

/-! ### Relative trees as edge sets -/

section RelTrees

open scoped Classical in
/-- A tree relative to `Y`, as an edge set: it joins distinct blocks, connects `V_Y` with the
blocks, and has `|Y| - 1` edges. -/
theorem relTree_pairs {Y : Finset (Finset ℕ)} (hY : IsSubpartition Y) {T : Finset (ℕ × ℕ)}
    (hT : T ∈ (relTrees Y).image edgesOf) :
    T ⊆ interPairs Y ∧ ConnOn (Y.biUnion id) (T ∪ intraPairs Y) ∧ T.card + 1 = Y.card := by
  obtain ⟨G, hG, rfl⟩ := mem_image.1 hT
  have hG' := mem_relTrees.1 hG
  refine ⟨(forall_adj_iff_edgesOf_subset_interPairs hY G).1
    (le_interEdges_iff.1 hG'.isRelConnected.le_interEdges),
    (connected_sup_iff G).1 hG'.isRelConnected.2.2, ?_⟩
  rw [card_edgesOf]
  exact IsRelTree₀.card_edgeFinset hY (Or.inl hG')

open scoped Classical in
/-- A tree of `𝖳_0^Y`, as an edge set. -/
theorem relTree₀_pairs {Y : Finset (Finset ℕ)} (hY : IsSubpartition Y) {T : Finset (ℕ × ℕ)}
    (hT : T ∈ (relTrees₀ Y).image edgesOf) :
    T ⊆ interPairs Y ∧ ConnOn (Y.biUnion id) (T ∪ intraPairs Y) ∧ T.card + 1 = Y.card := by
  obtain ⟨G, hG, rfl⟩ := mem_image.1 hT
  have hG' := mem_relTrees₀.1 hG
  refine ⟨(forall_adj_iff_edgesOf_subset_interPairs hY G).1
    (le_interEdges_iff.1 hG'.le_interEdges), ?_, ?_⟩
  · rcases hG' with h | ⟨h1, -⟩
    · exact (connected_sup_iff G).1 h.isRelConnected.2.2
    · exact (connected_sup_iff G).1 (connected_sup_intraEdges_of_card_eq_one hY h1 G)
  · rw [card_edgesOf]
    exact hG'.card_edgeFinset hY

end RelTrees

/-! ### Coarsenings -/

section Coarsen

variable {X : Finset (Finset ℕ)}

theorem exists_coarsen_superset (G : Finset (Finset (Finset ℕ))) {S : Finset ℕ} (hS : S ∈ X) :
    ∃ C ∈ coarsen X G, S ⊆ C := by
  by_cases h : ∃ Y ∈ G, S ∈ Y
  · obtain ⟨Y, hY, hSY⟩ := h
    exact ⟨Y.biUnion id, mem_union_left _ (mem_image_of_mem _ hY), subset_biUnion_of_mem id hSY⟩
  · push Not at h
    exact ⟨S, mem_union_right _ (mem_filter.2 ⟨hS, h⟩), subset_rfl⟩

theorem card_coarsen_add_le {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (hXsX : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l')) :
    (coarsen X ((univ : Finset (Fin n)).image Xs)).card + ∑ l, (Xs l).card ≤ n + X.card := by
  set Gs := (univ : Finset (Fin n)).image Xs with hGs
  set F := X.filter fun S : Finset ℕ => ∀ Y ∈ Gs, S ∉ Y with hF
  have h1 : (coarsen X Gs).card ≤ (Gs.image (fun Y => Y.biUnion id)).card + F.card :=
    card_union_le _ _
  have h2 : (Gs.image (fun Y => Y.biUnion id)).card ≤ n :=
    card_image_le.trans (card_image_le.trans (by rw [card_univ, Fintype.card_fin]))
  have hd : Disjoint F (univ.biUnion Xs) := by
    rw [Finset.disjoint_left]
    intro S hS hS'
    obtain ⟨l, -, hl⟩ := mem_biUnion.1 hS'
    exact (mem_filter.1 hS).2 (Xs l) (mem_image_of_mem _ (mem_univ l)) hl
  have h3 := card_union_of_disjoint hd
  have h5 := card_le_card (union_subset (filter_subset _ X) (biUnion_subset.2 fun l _ => hXsX l) :
    F ∪ univ.biUnion Xs ⊆ X)
  have h4 : (univ.biUnion Xs).card = ∑ l, (Xs l).card :=
    card_biUnion fun l _ l' _ h => hdisj l l' h
  omega

end Coarsen

/-! ### The structure of `T^a`, `T^b` on `V_X` -/

section Structure

variable {X : Finset (Finset ℕ)} {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)}
  {Ta : Fin n → Finset (ℕ × ℕ)} {Tb : Finset (ℕ × ℕ)}

theorem isSubpartition_of_subset {Y : Finset (Finset ℕ)} (hX : IsSubpartition X) (h : Y ⊆ X) :
    IsSubpartition Y :=
  ⟨fun S hS => hX.1 S (h hS), hX.2.subset (coe_subset.2 h)⟩

theorem mem_edgeFinset_graphOf_mk {U : Finset ℕ} {E : Finset (ℕ × ℕ)}
    [Fintype (graphOf U E).edgeSet] {a b : U} :
    s(a, b) ∈ (graphOf U E).edgeFinset ↔
      (a : ℕ) ≠ b ∧ (((a : ℕ), (b : ℕ)) ∈ E ∨ ((b : ℕ), (a : ℕ)) ∈ E) := by
  rw [mem_edgeFinset, mem_edgeSet, graphOf_adj, edgeGraph_adj]

/-- The group facts: `T^a_l` joins blocks of `X_l`, `|X_l| ≥ 1`, and `T^a_l ⊆ pairsOn V_X`. -/
theorem relTree_group (hX : IsSubpartition X) (hXsX : ∀ l, Xs l ⊆ X)
    (hTa : ∀ l, Ta l ∈ (relTrees (Xs l)).image edgesOf) (l : Fin n) :
    Ta l ⊆ interPairs (Xs l) ∧ ConnOn ((Xs l).biUnion id) (Ta l ∪ intraPairs (Xs l)) ∧
      (Ta l).card + 1 = (Xs l).card ∧ Ta l ⊆ pairsOn (X.biUnion id) := by
  obtain ⟨h1, h2, h3⟩ := relTree_pairs (isSubpartition_of_subset hX (hXsX l)) (hTa l)
  exact ⟨h1, h2, h3, h1.trans (interPairs_subset_pairsOn.trans
    (pairsOn_mono (biUnion_subset_biUnion_of_subset_left _ (hXsX l))))⟩

/-- The coarsening facts. -/
theorem relTree_coarse (hX : IsSubpartition X) (hXsX : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l'))
    (hTa : ∀ l, Ta l ∈ (relTrees (Xs l)).image edgesOf)
    (hTb : Tb ∈ (relTrees₀ (coarsen X ((univ : Finset (Fin n)).image Xs))).image edgesOf) :
    IsSubpartition (coarsen X ((univ : Finset (Fin n)).image Xs)) ∧
      (coarsen X ((univ : Finset (Fin n)).image Xs)).biUnion id = X.biUnion id ∧
      (∀ Y ∈ (univ : Finset (Fin n)).image Xs, Y ⊆ X) ∧
      ((((univ : Finset (Fin n)).image Xs : Finset (Finset (Finset ℕ))) :
        Set (Finset (Finset ℕ))).PairwiseDisjoint id) ∧
      Tb ⊆ interPairs (coarsen X ((univ : Finset (Fin n)).image Xs)) ∧
      ConnOn (X.biUnion id) (Tb ∪ intraPairs (coarsen X ((univ : Finset (Fin n)).image Xs))) ∧
      Tb.card + 1 = (coarsen X ((univ : Finset (Fin n)).image Xs)).card ∧
      Tb ⊆ pairsOn (X.biUnion id) := by
  have hGX : ∀ Y ∈ (univ : Finset (Fin n)).image Xs, Y ⊆ X := by
    intro Y hY
    obtain ⟨l, -, rfl⟩ := mem_image.1 hY
    exact hXsX l
  have hGne : ∀ Y ∈ (univ : Finset (Fin n)).image Xs, Y.Nonempty := by
    intro Y hY
    obtain ⟨l, -, rfl⟩ := mem_image.1 hY
    have := (relTree_group hX hXsX hTa l).2.2.1
    exact card_pos.1 (by omega)
  have hGd : ((((univ : Finset (Fin n)).image Xs : Finset (Finset (Finset ℕ))) :
      Set (Finset (Finset ℕ))).PairwiseDisjoint id) := by
    intro Y hY Y' hY' hne
    obtain ⟨l, -, rfl⟩ := mem_image.1 (mem_coe.1 hY)
    obtain ⟨l', -, rfl⟩ := mem_image.1 (mem_coe.1 hY')
    exact hdisj l l' fun h => hne (by rw [h])
  have hC := isSubpartition_coarsen hX hGX hGne hGd
  have hVC := biUnion_coarsen (X := X) hGX
  obtain ⟨h1, h2, h3⟩ := relTree₀_pairs hC hTb
  refine ⟨hC, hVC, hGX, hGd, h1, hVC ▸ h2, h3, ?_⟩
  rw [← hVC]
  exact h1.trans interPairs_subset_pairsOn

theorem blockOf_mem_subtype (hX : IsSubpartition X) {Y : Finset (Finset ℕ)} (hYX : Y ⊆ X)
    (i : X.biUnion id) (hi : (i : ℕ) ∈ Y.biUnion id) :
    Limits.blockOf X i ∈ Y.subtype (· ∈ X) := by
  obtain ⟨S, hS, hiS⟩ := mem_biUnion.1 hi
  rw [Limits.blockOf_eq hX (hYX hS) hiS, mem_subtype]
  exact hS

open scoped Classical in
/-- The structural hypotheses for the retained near, odd and even trees of Lemma A.4. -/
theorem trees_structure (hX : IsSubpartition X) (hXsX : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l'))
    (hTa : ∀ l, Ta l ∈ (relTrees (Xs l)).image edgesOf)
    (hTb : Tb ∈ (relTrees₀ (coarsen X ((univ : Finset (Fin n)).image Xs))).image edgesOf) :
    (∀ l l', l ≠ l' → Disjoint ((Xs l).subtype (· ∈ X)) ((Xs l').subtype (· ∈ X))) ∧
    (∀ l, ∀ e ∈ (graphOf (X.biUnion id) (Ta l)).edgeFinset, ∀ i ∈ e,
      Limits.blockOf X i ∈ (Xs l).subtype (· ∈ X)) ∧
    (∀ l, (graphOf (X.biUnion id) (Ta l)).edgeFinset.card + 1 = ((Xs l).subtype (· ∈ X)).card) ∧
    (∀ e ∈ univ.biUnion (fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset) ∪
      (graphOf (X.biUnion id) Tb).edgeFinset, ¬ (Sym2.map (Limits.blockOf X) e).IsDiag) ∧
    (∀ i j : X.biUnion id, (sameBlockGraph (Limits.blockOf X) ⊔
      fromEdgeSet ((univ.biUnion (fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset) ∪
        (graphOf (X.biUnion id) Tb).edgeFinset : Finset (Sym2 (X.biUnion id))) :
          Set (Sym2 (X.biUnion id)))).Reachable i j) ∧
    (∑ l, (graphOf (X.biUnion id) (Ta l)).edgeFinset.card +
      (graphOf (X.biUnion id) Tb).edgeFinset.card + 1 ≤ Fintype.card X) := by
  have hG := relTree_group hX hXsX hTa
  obtain ⟨hC, hVC, hGX, hGd, hTbi, hTbc, hTbcard, hTbV⟩ := relTree_coarse hX hXsX hdisj hTa hTb
  have hcardG : ∀ l, ((Xs l).subtype (· ∈ X)).card = (Xs l).card := fun l => by
    rw [card_subtype, filter_true_of_mem fun S hS => hXsX l hS]
  -- the edges of `T^a_l` and `T^b` join distinct blocks
  have hinterA : ∀ l (a b : X.biUnion id), (((a : ℕ), (b : ℕ)) ∈ Ta l) →
      Limits.blockOf X a ≠ Limits.blockOf X b := by
    intro l a b hab
    obtain ⟨B, hB, B', hB', hBB', h1, h2⟩ := exists_of_mem_interPairs ((hG l).1 hab)
    rw [Limits.blockOf_eq hX (hXsX l hB) h1, Limits.blockOf_eq hX (hXsX l hB') h2]
    exact fun h => hBB' (congrArg Subtype.val h)
  have hinterB : ∀ (a b : X.biUnion id), (((a : ℕ), (b : ℕ)) ∈ Tb) →
      Limits.blockOf X a ≠ Limits.blockOf X b := by
    intro a b hab heq
    obtain ⟨C, hC1, C', hC'1, hCC', h1, h2⟩ := exists_of_mem_interPairs (hTbi hab)
    obtain ⟨S'', hS'', -⟩ := (Limits.blockOf X a).2 |> fun h => (⟨_, h, rfl⟩ : ∃ S ∈ X, S = _)
    have haS := Limits.mem_blockOf a
    have hbS : (b : ℕ) ∈ ((Limits.blockOf X a : X) : Finset ℕ) := heq ▸ Limits.mem_blockOf b
    obtain ⟨C'', hC''1, hSC''⟩ :=
      exists_coarsen_superset ((univ : Finset (Fin n)).image Xs) (Limits.blockOf X a).2
    have e1 := eq_of_mem_of_mem_coarsen hX hGX hGd hC1 hC''1 h1 (hSC'' haS)
    have e2 := eq_of_mem_of_mem_coarsen hX hGX hGd hC'1 hC''1 h2 (hSC'' hbS)
    exact hCC' (e1.trans e2.symm)
  refine ⟨fun l l' hll' => Finset.disjoint_left.2 fun S hS hS' =>
      Finset.disjoint_left.1 (hdisj l l' hll') (mem_subtype.1 hS) (mem_subtype.1 hS'), ?_, ?_, ?_,
      ?_, ?_⟩
  · -- the edges of `T^a_l` join blocks of `X_l`
    intro l e he i hi
    induction e using Sym2.ind with
    | h a b =>
      obtain ⟨-, hab | hab⟩ := mem_edgeFinset_graphOf_mk.1 he
      · have hp := mem_pairsOn.1 (interPairs_subset_pairsOn ((hG l).1 hab))
        rcases Sym2.mem_iff.1 hi with rfl | rfl
        · exact blockOf_mem_subtype hX (hXsX l) _ hp.1
        · exact blockOf_mem_subtype hX (hXsX l) _ hp.2.1
      · have hp := mem_pairsOn.1 (interPairs_subset_pairsOn ((hG l).1 hab))
        rcases Sym2.mem_iff.1 hi with rfl | rfl
        · exact blockOf_mem_subtype hX (hXsX l) _ hp.2.1
        · exact blockOf_mem_subtype hX (hXsX l) _ hp.1
  · intro l
    rw [card_edgeFinset_graphOf (hG l).2.2.2, hcardG]
    exact (hG l).2.2.1
  · intro e he
    induction e using Sym2.ind with
    | h a b =>
      rw [Sym2.map_mk, Sym2.mk_isDiag_iff]
      rcases mem_union.1 he with he | he
      · obtain ⟨l, -, he⟩ := mem_biUnion.1 he
        obtain ⟨-, hab | hab⟩ := mem_edgeFinset_graphOf_mk.1 he
        · exact hinterA l a b hab
        · exact fun h => hinterA l b a hab h.symm
      · obtain ⟨-, hab | hab⟩ := mem_edgeFinset_graphOf_mk.1 he
        · exact hinterB a b hab
        · exact fun h => hinterB b a hab h.symm
  · -- connectivity
    intro i j
    set H := sameBlockGraph (Limits.blockOf X) ⊔
      fromEdgeSet ((univ.biUnion (fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset) ∪
        (graphOf (X.biUnion id) Tb).edgeFinset : Finset (Sym2 (X.biUnion id))) :
          Set (Sym2 (X.biUnion id))) with hH
    have hsame : ∀ (B : Finset ℕ), B ∈ X → ∀ (a b : X.biUnion id), (a : ℕ) ∈ B → (b : ℕ) ∈ B →
        H.Reachable a b := by
      intro B hB a b ha hb
      by_cases hab : a = b
      · rw [hab]
      · refine Adj.reachable (sup_adj _ _ _ _ |>.2 (Or.inl (sameBlockGraph_adj.2 ⟨hab, ?_⟩)))
        rw [Limits.blockOf_eq hX hB ha, Limits.blockOf_eq hX hB hb]
    have hedge : ∀ (a b : X.biUnion id), (a : ℕ) ≠ b →
        s(a, b) ∈ univ.biUnion (fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset) ∪
          (graphOf (X.biUnion id) Tb).edgeFinset → H.Reachable a b := by
      intro a b hab hmem
      refine Adj.reachable (sup_adj _ _ _ _ |>.2 (Or.inr ?_))
      rw [fromEdgeSet_adj]
      exact ⟨mem_coe.2 hmem, fun h => hab (congrArg Subtype.val h)⟩
    -- inside a group
    have hgroup : ∀ l (a b : X.biUnion id), (a : ℕ) ∈ (Xs l).biUnion id →
        (b : ℕ) ∈ (Xs l).biUnion id →
        H.Reachable a b := by
      intro l a b ha hb
      refine reachable_of_connOn_lift H (biUnion_subset_biUnion_of_subset_left _ (hXsX l))
        (union_subset ((hG l).1.trans interPairs_subset_pairsOn) intraPairs_subset_pairsOn)
        ?_ (hG l).2.1 ha hb
      intro p hp h1 h2
      rcases mem_union.1 hp with hp | hp
      · have hlt := (mem_pairsOn.1 ((hG l).2.2.2 hp)).2.2
        exact hedge _ _ hlt.ne (mem_union_left _ (mem_biUnion.2 ⟨l, mem_univ _,
          mem_edgeFinset_graphOf_mk.2 ⟨hlt.ne, Or.inl hp⟩⟩))
      · obtain ⟨B, hB, hpB⟩ := mem_intraPairs.1 hp
        have hpB' := mem_pairsOn.1 hpB
        exact hsame B (hXsX l hB) _ _ hpB'.1 hpB'.2.1
    refine reachable_of_connOn_lift H subset_rfl
      (union_subset hTbV (hVC ▸ intraPairs_subset_pairsOn)) ?_ hTbc i.2 j.2
    intro p hp h1 h2
    rcases mem_union.1 hp with hp | hp
    · have hlt := (mem_pairsOn.1 (hTbV hp)).2.2
      exact hedge _ _ hlt.ne (mem_union_right _ (mem_edgeFinset_graphOf_mk.2 ⟨hlt.ne, Or.inl hp⟩))
    · obtain ⟨C, hC', hpC⟩ := mem_intraPairs.1 hp
      have hpC' := mem_pairsOn.1 hpC
      rcases mem_union.1 hC' with hC' | hC'
      · obtain ⟨Y, hY, rfl⟩ := mem_image.1 hC'
        obtain ⟨l, -, rfl⟩ := mem_image.1 hY
        exact hgroup l _ _ hpC'.1 hpC'.2.1
      · exact hsame C (mem_filter.1 hC').1 _ _ hpC'.1 hpC'.2.1
  · -- the count
    have hcA : ∀ l, (graphOf (X.biUnion id) (Ta l)).edgeFinset.card + 1 = (Xs l).card := fun l => by
      rw [card_edgeFinset_graphOf (hG l).2.2.2]
      exact (hG l).2.2.1
    have hsum : ∑ l, (graphOf (X.biUnion id) (Ta l)).edgeFinset.card + n =
        ∑ l, (Xs l).card := by
      rw [← sum_congr rfl fun l _ => hcA l, sum_add_distrib, sum_const, card_univ,
        Fintype.card_fin, smul_eq_mul, mul_one]
    have hcB : (graphOf (X.biUnion id) Tb).edgeFinset.card + 1 =
        (coarsen X ((univ : Finset (Fin n)).image Xs)).card := by
      rw [card_edgeFinset_graphOf hTbV]
      exact hTbcard
    have hle := card_coarsen_add_le Xs hXsX hdisj
    rw [Fintype.card_coe]
    omega

end Structure

end SmallIntegral

end MultipoleBKT

end
