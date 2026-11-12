/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Cluster.Relative
public import MultipoleBKT.Multipole.EdgeSets
public import MultipoleBKT.LowerBound.Hierarchical.Euler
public import MultipoleBKT.UpperBound.CoreForest.EulerOff

/-!
# Edge sets of labels and graphs on `V_X`

The activities of the hierarchical models are written with edge sets `E ⊆ pairsOn V` of pairs
`(i, j)`, `i < j`, of labels (`MultipoleBKT.Multipole.EdgeSets`), while the relative graph notions
of Definitions 4.9–4.10 (`MultipoleBKT.Cluster.Relative`), the peeling of §4.6
(`MultipoleBKT.LowerBound.Peeling`) and the core-forest decomposition of §5.4
(`MultipoleBKT.UpperBound.CoreForest`) work with simple graphs on the type `V_X = X.biUnion id`.
This file translates between them.

* `pairGraph W E`, the graph on `W` of an edge set; `graphPairs G`, the edge set of a graph on `W`;
  `graphPairs_pairGraph`, `prod_graphPairs` (`∏_{(i,j)} f(i, j) = ∏_{e ∈ E(G)} f_e` for symmetric
  `f`), `prod_pairs_eq_prod_edgeFinset`;
* `pairGraph_le_interEdges`, `pairGraph_intraPairs`, `pairGraph_union`;
* `blockDegree_pairGraph`: `deg_E(S)` (Definition 4.10(7)) is `blockDeg E S`;
* `connected_pairGraph_of_connOn`: `ConnOn W F` gives the connectedness of `pairGraph W F`;
* `exists_isRelTree₀_le`: a graph `G ≤ ℰ^inter(X)` with `G ∪ ℰ^intra(X)` connected contains a
  relative tree `T ∈ 𝖳_0^X` (a minimal connecting subgraph is a relative forest).
-/

@[expose] public section

open Finset SimpleGraph

namespace MultipoleBKT

namespace UpperBound

namespace BoundedUpper

open Multipole Hierarchical

/-! ### Graphs and edge sets -/

section Graph

variable {W : Finset ℕ}

/-- The graph on `W` of an edge set of pairs of labels. -/
def pairGraph (W : Finset ℕ) (E : Finset (ℕ × ℕ)) : SimpleGraph W :=
  SimpleGraph.fromRel fun i j => ((i : ℕ), (j : ℕ)) ∈ E

theorem pairGraph_adj {E : Finset (ℕ × ℕ)} {i j : W} :
    (pairGraph W E).Adj i j ↔ i ≠ j ∧ (((i : ℕ), (j : ℕ)) ∈ E ∨ ((j : ℕ), (i : ℕ)) ∈ E) :=
  SimpleGraph.fromRel_adj _ _ _

theorem pairGraph_mono {E F : Finset (ℕ × ℕ)} (h : E ⊆ F) : pairGraph W E ≤ pairGraph W F := by
  intro i j hij
  rw [pairGraph_adj] at hij ⊢
  exact ⟨hij.1, hij.2.imp (fun h' => h h') (fun h' => h h')⟩

theorem pairGraph_union (E F : Finset (ℕ × ℕ)) :
    pairGraph W (E ∪ F) = pairGraph W E ⊔ pairGraph W F := by
  ext i j
  simp only [pairGraph_adj, sup_adj, Finset.mem_union]
  tauto

open scoped Classical in
/-- The edge set of pairs `(i, j)`, `i < j`, of a graph on `W`. -/
noncomputable def graphPairs (G : SimpleGraph W) : Finset (ℕ × ℕ) :=
  ((univ ×ˢ univ).filter fun p : W × W => p.1 < p.2 ∧ G.Adj p.1 p.2).map
    ⟨fun p => ((p.1 : ℕ), (p.2 : ℕ)), fun p q h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)⟩

theorem mem_graphPairs {G : SimpleGraph W} {p : ℕ × ℕ} :
    p ∈ graphPairs G ↔ ∃ (h1 : p.1 ∈ W) (h2 : p.2 ∈ W), p.1 < p.2 ∧ G.Adj ⟨p.1, h1⟩ ⟨p.2, h2⟩ := by
  classical
  simp only [graphPairs, Finset.mem_map, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨⟨i, j⟩, ⟨hij, hadj⟩, rfl⟩
    exact ⟨i.2, j.2, hij, hadj⟩
  · rintro ⟨h1, h2, h12, hadj⟩
    exact ⟨(⟨p.1, h1⟩, ⟨p.2, h2⟩), ⟨h12, hadj⟩, rfl⟩

theorem graphPairs_subset_pairsOn (G : SimpleGraph W) : graphPairs G ⊆ pairsOn W := by
  intro p hp
  obtain ⟨h1, h2, h12, -⟩ := mem_graphPairs.1 hp
  exact mem_pairsOn.2 ⟨h1, h2, h12⟩

theorem graphPairs_mono {G G' : SimpleGraph W} (h : G ≤ G') : graphPairs G ⊆ graphPairs G' := by
  intro p hp
  obtain ⟨h1, h2, h12, hadj⟩ := mem_graphPairs.1 hp
  exact mem_graphPairs.2 ⟨h1, h2, h12, h hadj⟩

theorem graphPairs_pairGraph {E : Finset (ℕ × ℕ)} (hE : E ⊆ pairsOn W) :
    graphPairs (pairGraph W E) = E := by
  ext p
  rw [mem_graphPairs]
  constructor
  · rintro ⟨h1, h2, h12, hadj⟩
    rw [pairGraph_adj] at hadj
    rcases hadj.2 with h | h
    · exact h
    · exact absurd h12 (not_lt.2 (mem_pairsOn.1 (hE h)).2.2.le)
  · intro hp
    obtain ⟨h1, h2, h12⟩ := mem_pairsOn.1 (hE hp)
    exact ⟨h1, h2, h12, pairGraph_adj.2 ⟨fun h => h12.ne (congrArg Subtype.val h), Or.inl hp⟩⟩

open scoped Classical in
/-- For a symmetric `f`, the product of `f` over the pairs of a graph is the product over its
edges. -/
theorem prod_graphPairs {M : Type*} [CommMonoid M] (G : SimpleGraph W) (f : ℕ → ℕ → M)
    (hf : ∀ i j, f i j = f j i) :
    ∏ p ∈ graphPairs G, f p.1 p.2 =
      ∏ e ∈ G.edgeFinset, Sym2.lift ⟨fun i j : W => f i j, fun i j => hf i j⟩ e := by
  rw [graphPairs, Finset.prod_map]
  refine Finset.prod_bij (fun p _ => s(p.1, p.2)) (fun p hp => ?_) (fun p hp q hq h => ?_)
    (fun e he => ?_) (fun p hp => ?_)
  · rw [mem_edgeFinset]
    exact (mem_filter.1 hp).2.2
  · have hp' := (mem_filter.1 hp).2.1
    have hq' := (mem_filter.1 hq).2.1
    rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · rw [h1, h2] at hp'
      exact absurd hq' (not_lt.2 hp'.le)
  · induction e using Sym2.ind with
    | h i j =>
      rw [mem_edgeFinset] at he
      rcases lt_or_gt_of_ne he.ne with h | h
      · exact ⟨(i, j), mem_filter.2 ⟨mem_product.2 ⟨mem_univ _, mem_univ _⟩, h, he⟩, rfl⟩
      · exact ⟨(j, i), mem_filter.2 ⟨mem_product.2 ⟨mem_univ _, mem_univ _⟩, h, he.symm⟩,
          Sym2.eq_swap⟩
  · rfl

open scoped Classical in
/-- `∏_{(i,j) ∈ E} f(i, j) = ∏_{e ∈ E(pairGraph W E)} f_e` for `E ⊆ pairsOn W` and symmetric `f`. -/
theorem prod_pairs_eq_prod_edgeFinset {M : Type*} [CommMonoid M] {E : Finset (ℕ × ℕ)}
    (hE : E ⊆ pairsOn W) (f : ℕ → ℕ → M) (hf : ∀ i j, f i j = f j i) :
    ∏ p ∈ E, f p.1 p.2 =
      ∏ e ∈ (pairGraph W E).edgeFinset, Sym2.lift ⟨fun i j : W => f i j, fun i j => hf i j⟩ e := by
  rw [← prod_graphPairs, graphPairs_pairGraph hE]

/-- `ConnOn W F` (with `F ⊆ pairsOn W`) gives the connectedness of `pairGraph W F`. -/
theorem connected_pairGraph_of_connOn {F : Finset (ℕ × ℕ)} (hF : F ⊆ pairsOn W)
    (h : ConnOn W F) : (pairGraph W F).Connected := by
  have hne : Nonempty W := by
    obtain ⟨i, hi⟩ := h.1
    exact ⟨⟨i, hi⟩⟩
  refine ⟨fun i j => ?_⟩
  have hij := h.2 i i.2 j j.2
  suffices key : ∀ (u v : ℕ) (w : (edgeGraph F).Walk u v) (hu : u ∈ W) (hv : v ∈ W),
      (pairGraph W F).Reachable ⟨u, hu⟩ ⟨v, hv⟩ by
    obtain ⟨w⟩ := hij
    exact key _ _ w i.2 j.2
  intro u v w
  induction w with
  | nil => intro hu hv; exact Reachable.refl _
  | @cons u u' v hadj w ih =>
    intro hu hv
    have hu' := (mem_of_edgeGraph_adj hF hadj).2
    refine Reachable.trans ?_ (ih hu' hv)
    refine Adj.reachable (pairGraph_adj.2 ⟨fun h => ?_, ?_⟩)
    · exact (edgeGraph_adj.1 hadj).1 (congrArg Subtype.val h)
    · exact (edgeGraph_adj.1 hadj).2

end Graph

/-! ### Relative notions -/

section Relative

variable {X : Finset (Finset ℕ)}

theorem pairGraph_le_interEdges {E : Finset (ℕ × ℕ)} (hE : E ⊆ interPairs X) :
    pairGraph (X.biUnion id) E ≤ interEdges X := by
  intro i j hij
  rw [pairGraph_adj] at hij
  rw [interEdges, fromRel_adj]
  refine ⟨hij.1, ?_⟩
  rcases hij.2 with h | h
  · obtain ⟨B, hB, B', hB', hBB', h1, h2⟩ := exists_of_mem_interPairs (hE h)
    exact Or.inl ⟨B, hB, B', hB', hBB', h1, h2⟩
  · obtain ⟨B, hB, B', hB', hBB', h1, h2⟩ := exists_of_mem_interPairs (hE h)
    exact Or.inr ⟨B, hB, B', hB', hBB', h1, h2⟩

theorem pairGraph_intraPairs :
    pairGraph (X.biUnion id) (intraPairs X) = intraEdges X := by
  ext i j
  rw [pairGraph_adj, intraEdges, fromRel_adj]
  refine and_congr_right fun hne => ?_
  constructor
  · rintro (h | h)
    · obtain ⟨B, hB, hp⟩ := mem_intraPairs.1 h
      exact Or.inl ⟨B, hB, (mem_pairsOn.1 hp).1, (mem_pairsOn.1 hp).2.1⟩
    · obtain ⟨B, hB, hp⟩ := mem_intraPairs.1 h
      exact Or.inr ⟨B, hB, (mem_pairsOn.1 hp).1, (mem_pairsOn.1 hp).2.1⟩
  · intro h
    have hne' : (i : ℕ) ≠ j := fun h' => hne (Subtype.ext h')
    have h' : ∃ B ∈ X, (i : ℕ) ∈ B ∧ (j : ℕ) ∈ B := by
      rcases h with ⟨B, hB, hi, hj⟩ | ⟨B, hB, hj, hi⟩
      · exact ⟨B, hB, hi, hj⟩
      · exact ⟨B, hB, hi, hj⟩
    obtain ⟨B, hB, hi, hj⟩ := h'
    rcases lt_or_gt_of_ne hne' with hlt | hlt
    · exact Or.inl (mem_intraPairs.2 ⟨B, hB, mem_pairsOn.2 ⟨hi, hj, hlt⟩⟩)
    · exact Or.inr (mem_intraPairs.2 ⟨B, hB, mem_pairsOn.2 ⟨hj, hi, hlt⟩⟩)

/-- `ConnOn V_X (E ∪ ℰ^intra(X))` gives the connectedness of `pairGraph V_X E ∪ ℰ^intra(X)`. -/
theorem connected_sup_intraEdges_of_connOn {E : Finset (ℕ × ℕ)}
    (hE : E ⊆ interPairs X) (h : ConnOn (X.biUnion id) (E ∪ intraPairs X)) :
    (pairGraph (X.biUnion id) E ⊔ intraEdges X).Connected := by
  rw [← pairGraph_intraPairs, ← pairGraph_union]
  exact connected_pairGraph_of_connOn (Finset.union_subset (hE.trans interPairs_subset_pairsOn)
    intraPairs_subset_pairsOn) h

open scoped Classical in
/-- `deg_E(S) = ∑_{i ∈ S} deg_E(i)` (Definition 4.10(7)) of the graph of an edge set is the count
`blockDeg E S` of the pairs of `E` with an endpoint in `S`. -/
theorem blockDegree_pairGraph {E : Finset (ℕ × ℕ)} (hE : E ⊆ pairsOn (X.biUnion id))
    {S : Finset ℕ} (hS : S ⊆ X.biUnion id) :
    blockDegree X (pairGraph (X.biUnion id) E) S = blockDeg E S := by
  set W := X.biUnion id
  set G := pairGraph W E
  -- the degree of a vertex
  have hdeg : ∀ i : W, G.degree i =
      (E.filter fun p => p.1 = (i : ℕ)).card + (E.filter fun p => p.2 = (i : ℕ)).card := by
    intro i
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
    have h1 : (univ.filter (G.Adj i)) =
        (univ.filter fun j : W => ((i : ℕ), (j : ℕ)) ∈ E) ∪
          (univ.filter fun j : W => ((j : ℕ), (i : ℕ)) ∈ E) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      rw [pairGraph_adj]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨fun hij => ?_, h⟩
        subst hij
        rcases h with h | h <;> exact absurd (mem_pairsOn.1 (hE h)).2.2 (lt_irrefl _)
    have hdisj : Disjoint (univ.filter fun j : W => ((i : ℕ), (j : ℕ)) ∈ E)
        (univ.filter fun j : W => ((j : ℕ), (i : ℕ)) ∈ E) := by
      rw [Finset.disjoint_filter]
      intro j _ h1 h2
      have a := (mem_pairsOn.1 (hE h1)).2.2
      have b := (mem_pairsOn.1 (hE h2)).2.2
      exact absurd (a.trans b) (lt_irrefl _)
    rw [h1, Finset.card_union_of_disjoint hdisj]
    congr 1
    · refine Finset.card_bij (fun j _ => ((i : ℕ), (j : ℕ))) (fun j hj => ?_)
        (fun j _ j' _ h => Subtype.ext (congrArg Prod.snd h)) (fun p hp => ?_)
      · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hj).2, rfl⟩
      · obtain ⟨hpE, hp1⟩ := Finset.mem_filter.1 hp
        have h2 := (mem_pairsOn.1 (hE hpE)).2.1
        refine ⟨⟨p.2, h2⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · rw [← hp1]
          exact hpE
        · rw [← hp1]
    · refine Finset.card_bij (fun j _ => ((j : ℕ), (i : ℕ))) (fun j hj => ?_)
        (fun j _ j' _ h => Subtype.ext (congrArg Prod.fst h)) (fun p hp => ?_)
      · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hj).2, rfl⟩
      · obtain ⟨hpE, hp2⟩ := Finset.mem_filter.1 hp
        have h1 := (mem_pairsOn.1 (hE hpE)).1
        refine ⟨⟨p.1, h1⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · rw [← hp2]
          exact hpE
        · rw [← hp2]
  unfold blockDegree blockDeg
  simp_rw [hdeg]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [← Finset.card_biUnion]
    · congr 1
      ext p
      simp only [Finset.mem_biUnion, Finset.mem_subtype, Finset.mem_filter]
      constructor
      · rintro ⟨i, hi, hpE, hpi⟩
        exact ⟨hpE, hpi ▸ hi⟩
      · rintro ⟨hpE, hp⟩
        exact ⟨⟨p.1, hS hp⟩, hp, hpE, rfl⟩
    · intro i _ j _ hij
      rw [Function.onFun, Finset.disjoint_filter]
      intro p _ h1 h2
      exact hij (Subtype.ext (h1.symm.trans h2))
  · rw [← Finset.card_biUnion]
    · congr 1
      ext p
      simp only [Finset.mem_biUnion, Finset.mem_subtype, Finset.mem_filter]
      constructor
      · rintro ⟨i, hi, hpE, hpi⟩
        exact ⟨hpE, hpi ▸ hi⟩
      · rintro ⟨hpE, hp⟩
        exact ⟨⟨p.2, hS hp⟩, hp, hpE, rfl⟩
    · intro i _ j _ hij
      rw [Function.onFun, Finset.disjoint_filter]
      intro p _ h1 h2
      exact hij (Subtype.ext (h1.symm.trans h2))

/-- **A relative spanning tree.** If `G ≤ ℰ^inter(X)` and `G ∪ ℰ^intra(X)` is connected, then some
`T ≤ G` is a tree relative to `X` (`T ∈ 𝖳_0^X`): a minimal `T ≤ G` keeping `T ∪ ℰ^intra(X)`
connected is a forest relative to `ℰ^intra(X)`. -/
theorem exists_isRelTree₀_le (hX : IsSubpartition X) {G : SimpleGraph (X.biUnion id)}
    (hG : G ≤ interEdges X) (hc : (G ⊔ intraEdges X).Connected) :
    ∃ T ≤ G, IsRelTree₀ X T := by
  classical
  obtain ⟨T, ⟨hTG, hTc⟩, hmin⟩ := WellFounded.has_min wellFounded_lt
    {T : SimpleGraph (X.biUnion id) | T ≤ G ∧ (T ⊔ intraEdges X).Connected} ⟨G, le_rfl, hc⟩
  refine ⟨T, hTG, (isRelTree₀_iff hX).2 ⟨hTG.trans hG, hTc, fun u v huv hreach => ?_⟩⟩
  set T' := T.deleteEdges {s(u, v)}
  have hT'T : T' < T := by
    refine lt_of_le_of_ne (deleteEdges_le _) fun h => ?_
    have : T'.Adj u v := by rw [h]; exact huv
    rw [deleteEdges_adj] at this
    exact this.2 rfl
  apply hmin T' ⟨(deleteEdges_le _).trans hTG, ?_⟩ hT'T
  have hne := hTc.nonempty
  refine ⟨fun x y => ?_⟩
  refine reachable_comp_of_forall_adj id (fun a b hab => ?_) (hTc.preconnected x y)
  rcases hab with hab | hab
  · by_cases he : s(a, b) = s(u, v)
    · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [sup_comm]
        exact hreach
      · rw [sup_comm]
        exact hreach.symm
    · exact Adj.reachable (Or.inl (deleteEdges_adj.2 ⟨hab, by simpa using he⟩))
  · exact Adj.reachable (Or.inr hab)

end Relative

end BoundedUpper

end UpperBound

end MultipoleBKT

end
