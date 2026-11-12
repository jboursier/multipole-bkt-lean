/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Cluster.Relative
public import MultipoleBKT.Cluster.Rota
public import Mathlib.Data.Sym.Sym2.Order

/-!
# Kruskal's algorithm relative to a subpartition and the Penrose resummation

We formalize Definition 4.50 and Lemma 4.51 (equation (4.86)) of the
paper.

Fix a subpartition `X`. The edges of `ℰ^inter(X)` are ordered lexicographically: an edge `ij`
is compared through the pair `(min(i, j), max(i, j))` (`MultipoleBKT.lexKey`), and we use its
rank `MultipoleBKT.lexRank` in this order as an injective weight.

* `MultipoleBKT.kruskalTree X H`: the relative Kruskal map `𝒯^KA_X(H)`. It keeps the edges `uv`
  of `H` whose endpoints are not joined by `ℰ^intra(X)` together with the edges of `H` that are
  lexicographically smaller than `uv`. This is the paper's greedy procedure: an edge is kept
  iff it does not form a cycle relative to `X` with the previously kept edges
  (`MultipoleBKT.kruskalTree_adj_iff_not_hasRelCycle`). It maps `𝖤_0^X` into `𝖳_0^X`
  (`MultipoleBKT.IsRelConnected₀.isRelTree₀_kruskalTree`).
* `MultipoleBKT.kruskalMax X T`: the set `𝓔^KA_max(X, T)`, formed by `T` and the edges `uv` of
  `ℰ^inter(X)` whose endpoints are joined by `ℰ^intra(X)` and the edges of `T` smaller than `uv`.
  It is the greatest element of the fibre of `𝒯^KA_X` over `T`
  (`MultipoleBKT.isGreatest_kruskalMax`), which is how the paper defines it.
* `MultipoleBKT.kruskalTree_eq_iff_sdiff`: for `H ∈ 𝖤_0^X` and `T ∈ 𝖳_0^X`,
  `𝒯^KA_X(H) = T ⟺ T ⊆ H ∧ H ∖ T ⊆ 𝓔^KA_max(X, T) ∖ T`.
* `MultipoleBKT.penrose`: the Penrose resummation (4.86),
`∑_{H ∈ 𝖤_0^X} ∏_{ij ∈ H} c_ij`
  `= ∑_{T ∈ 𝖳_0^X} ∏_{ij ∈ T} c_ij ∏_{ij ∈ 𝓔^KA_max(X,T) ∖ T} (1 + c_ij)`, for weights in any
  commutative semiring, and two consequences used in Section 4:
  `MultipoleBKT.penrose_le` (nonnegative weights) and `MultipoleBKT.abs_penrose_le`
  (weights with `|1 + c_ij| ≤ 1`).
* `MultipoleBKT.kruskalMax_adj_iff_path`: the paper's construction of `𝓔^KA_max(X, T)` through
  the path of the quotient tree; `MultipoleBKT.eq_kruskalTree_iff`: `𝒯^KA_X(H)` is the unique
  output of the greedy procedure; `MultipoleBKT.prod_prod_ite_lt_adj`: products over pairs
  `i < j` (the form of the frozen activity) are products over edges.

The relative Kruskal forest is built for an arbitrary base graph `K` (`MultipoleBKT.relKruskal`);
for `K = ⊥` it is the Kruskal forest `MultipoleBKT.kruskalForest` used for Rota's bound
(`MultipoleBKT.relKruskal_bot`).
-/

@[expose] public section

namespace MultipoleBKT

open Finset SimpleGraph

section RelKruskal

variable {V : Type*} (K : SimpleGraph V) (w : Sym2 V → ℕ)

/-- The Kruskal forest of `H` relative to a base graph `K`, for the edge weights `w`: the edges
`uv` of `H` whose endpoints are not joined in `K` together with the edges of `H` lighter than
`uv`. For `K = ⊥` this is `MultipoleBKT.kruskalForest` (`MultipoleBKT.relKruskal_bot`). -/
def relKruskal (H : SimpleGraph V) : SimpleGraph V where
  Adj u v := H.Adj u v ∧ ¬ (K ⊔ lighter w H (w s(u, v))).Reachable u v
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact fun hr => h.2 hr.symm⟩⟩
  loopless := ⟨fun u h => h.1.ne rfl⟩

/-- The largest graph with relative Kruskal forest `T` among the subgraphs of `L`: the edges of
`T`, and the edges `uv` of `L` whose endpoints are joined in `K` together with the edges of `T`
lighter than `uv` (`MultipoleBKT.relKruskal_eq_iff`). -/
def relKruskalMax (L T : SimpleGraph V) : SimpleGraph V where
  Adj u v := T.Adj u v ∨ (L.Adj u v ∧ (K ⊔ lighter w T (w s(u, v))).Reachable u v)
  symm := ⟨fun u v h => h.imp (fun h => h.symm) fun h =>
    ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2.symm⟩⟩
  loopless := ⟨fun u h => h.elim (fun h => h.ne rfl) fun h => h.1.ne rfl⟩

variable {K w}

theorem relKruskal_adj {H : SimpleGraph V} {u v : V} :
    (relKruskal K w H).Adj u v ↔ H.Adj u v ∧ ¬ (K ⊔ lighter w H (w s(u, v))).Reachable u v :=
  Iff.rfl

theorem relKruskalMax_adj {L T : SimpleGraph V} {u v : V} :
    (relKruskalMax K w L T).Adj u v ↔
      T.Adj u v ∨ (L.Adj u v ∧ (K ⊔ lighter w T (w s(u, v))).Reachable u v) :=
  Iff.rfl

theorem relKruskal_le (H : SimpleGraph V) : relKruskal K w H ≤ H := fun _ _ h => h.1

theorem le_relKruskalMax (L T : SimpleGraph V) : T ≤ relKruskalMax K w L T :=
  fun _ _ h => Or.inl h

theorem relKruskalMax_le (L T : SimpleGraph V) : relKruskalMax K w L T ≤ T ⊔ L :=
  fun _ _ h => h.imp id fun h => h.1

/-- For the empty base graph, the relative Kruskal forest is the Kruskal forest. -/
theorem relKruskal_bot (H : SimpleGraph V) : relKruskal ⊥ w H = kruskalForest w H := by
  ext u v
  rw [relKruskal_adj, kruskalForest_adj, bot_sup_eq]

/-- Edges of `K` and of `H` lighter than `n` connect what edges of `K` and of the relative
Kruskal forest lighter than `n` connect. -/
theorem reachable_lighter_relKruskal (H : SimpleGraph V) (n : ℕ) {u v : V}
    (h : (K ⊔ lighter w H n).Reachable u v) :
    (K ⊔ lighter w (relKruskal K w H) n).Reachable u v := by
  induction n using Nat.strong_induction_on generalizing u v with
  | _ n ih =>
    refine reachable_of_forall_adj_reachable (fun x y hxy => ?_) h
    rcases hxy with hxy | hxy
    · exact Adj.reachable (Or.inl hxy)
    · rw [lighter_adj] at hxy
      by_cases hT : (relKruskal K w H).Adj x y
      · exact Adj.reachable (Or.inr (lighter_adj.mpr ⟨hT, hxy.2⟩))
      · have hr : (K ⊔ lighter w H (w s(x, y))).Reachable x y := by
          by_contra hr
          exact hT ⟨hxy.1, hr⟩
        exact (ih _ hxy.2 hr).mono (sup_le_sup_left (lighter_mono_right _ hxy.2.le) K)

/-- The relative Kruskal forest is the result of the greedy procedure: an edge `uv` of `H` is
kept iff its endpoints are not joined in `K` together with the kept edges lighter than `uv`. -/
theorem relKruskal_adj_iff {H : SimpleGraph V} {u v : V} :
    (relKruskal K w H).Adj u v ↔
      H.Adj u v ∧ ¬ (K ⊔ lighter w (relKruskal K w H) (w s(u, v))).Reachable u v := by
  refine and_congr_right fun _ => not_congr ⟨reachable_lighter_relKruskal H _, fun h => ?_⟩
  exact h.mono (sup_le_sup_left (lighter_mono_left (relKruskal_le H) _) K)

/-- `K ∪ H` and `K ∪ (relative Kruskal forest of H)` have the same connected components. -/
theorem reachable_relKruskal {H : SimpleGraph V} {u v : V} (h : (K ⊔ H).Reachable u v) :
    (K ⊔ relKruskal K w H).Reachable u v := by
  refine reachable_of_forall_adj_reachable (fun x y hxy => ?_) h
  rcases hxy with hxy | hxy
  · exact Adj.reachable (Or.inl hxy)
  · by_cases hT : (relKruskal K w H).Adj x y
    · exact Adj.reachable (Or.inr hT)
    · have hr : (K ⊔ lighter w H (w s(x, y))).Reachable x y := by
        by_contra hr
        exact hT ⟨hxy, hr⟩
      exact (reachable_lighter_relKruskal H _ hr).mono (sup_le_sup_left (lighter_le _ _) K)

/-- For injective weights and `H` edge-disjoint from `K`, the relative Kruskal forest is a
forest relative to `K`: the heaviest edge of `T` on a cycle of `K ∪ T` would have its endpoints
joined by `K` and lighter edges of `T`. -/
theorem relKruskal_isRelForest (hw : Function.Injective w) {H : SimpleGraph V}
    (hHK : ∀ u v, H.Adj u v → ¬ K.Adj u v) : IsRelForest K (relKruskal K w H) := by
  classical
  intro u v huv hr
  set T := relKruskal K w H with hTdef
  have hle1 : K ⊔ T.deleteEdges {s(u, v)} ≤ (K ⊔ T).deleteEdges {s(u, v)} := by
    intro a b hab
    rw [deleteEdges_adj, sup_adj]
    rcases hab with hab | hab
    · refine ⟨Or.inl hab, fun hmem => ?_⟩
      rw [Set.mem_singleton_iff] at hmem
      rcases Sym2.eq_iff.mp hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hHK _ _ huv.1 hab
      · exact hHK _ _ huv.1 hab.symm
    · rw [deleteEdges_adj] at hab
      exact ⟨Or.inr hab.1, hab.2⟩
  obtain ⟨z, c, hc, he⟩ :=
    adj_and_reachable_delete_edges_iff_exists_cycle.mp ⟨Or.inr huv, hr.mono hle1⟩
  set F := c.edges.toFinset.filter (· ∈ T.edgeSet)
  have hF : F.Nonempty := ⟨s(u, v), mem_filter.mpr ⟨List.mem_toFinset.mpr he, huv⟩⟩
  obtain ⟨f, hfF, hmax⟩ := F.exists_max_image w hF
  rw [mem_filter, List.mem_toFinset] at hfF
  induction f using Sym2.ind with
  | h x y =>
    have hxy : T.Adj x y := hfF.2
    have hc' : ∀ e ∈ c.edges, e ∈ (K ⊔ lighter w T (w s(x, y) + 1)).edgeSet := by
      intro e he'
      have := c.edges_subset_edgeSet he'
      rw [edgeSet_sup] at this ⊢
      rcases this with hK | hT
      · exact Or.inl hK
      · right
        induction e using Sym2.ind with
        | h a b =>
          rw [mem_edgeSet, lighter_adj]
          exact ⟨hT, Nat.lt_succ_of_le
            (hmax _ (mem_filter.mpr ⟨List.mem_toFinset.mpr he', hT⟩))⟩
    have hcyc := (adj_and_reachable_delete_edges_iff_exists_cycle).mpr
      ⟨z, c.transfer _ hc', hc.transfer hc', by simpa using hfF.1⟩
    have hle2 : (K ⊔ lighter w T (w s(x, y) + 1)).deleteEdges {s(x, y)} ≤
        K ⊔ lighter w H (w s(x, y)) := by
      intro a b hab
      rw [deleteEdges_adj, sup_adj, Set.mem_singleton_iff] at hab
      obtain ⟨hab | hab, hne⟩ := hab
      · exact Or.inl hab
      · rw [lighter_adj] at hab
        refine Or.inr (lighter_adj.mpr ⟨relKruskal_le H hab.1, ?_⟩)
        exact lt_of_le_of_ne (Nat.lt_succ_iff.mp hab.2) fun h => hne (hw h)
    exact hxy.2 (hcyc.2.mono hle2)

/-- In a relative forest, the endpoints of an edge `uv` are not joined by `K` and the lighter
edges. -/
theorem not_reachable_lighter_of_isRelForest {T : SimpleGraph V} (hT : IsRelForest K T)
    {u v : V} (huv : T.Adj u v) : ¬ (K ⊔ lighter w T (w s(u, v))).Reachable u v := by
  refine fun hr => hT u v huv (hr.mono (sup_le_sup_left (fun a b hab => ?_) K))
  rw [lighter_adj] at hab
  refine deleteEdges_adj.mpr ⟨hab.1, fun hmem => ?_⟩
  rw [Set.mem_singleton_iff] at hmem
  rw [hmem] at hab
  exact lt_irrefl _ hab.2

/-- The fibres of the relative Kruskal map are intervals: for a relative forest `T` and
`H ≤ L`, the relative Kruskal forest of `H` is `T` iff `T ≤ H ≤ relKruskalMax K w L T`. -/
theorem relKruskal_eq_iff {L T H : SimpleGraph V} (hT : IsRelForest K T) (hHL : H ≤ L) :
    relKruskal K w H = T ↔ T ≤ H ∧ H ≤ relKruskalMax K w L T := by
  constructor
  · rintro rfl
    refine ⟨relKruskal_le H, fun u v huv => ?_⟩
    by_cases hT' : (relKruskal K w H).Adj u v
    · exact Or.inl hT'
    · refine Or.inr ⟨hHL huv, ?_⟩
      have hr : (K ⊔ lighter w H (w s(u, v))).Reachable u v := by
        by_contra hr
        exact hT' ⟨huv, hr⟩
      exact reachable_lighter_relKruskal H _ hr
  · rintro ⟨hTH, hHM⟩
    have key : ∀ n a b, (K ⊔ lighter w H n).Reachable a b →
        (K ⊔ lighter w T n).Reachable a b := by
      intro n a b h
      refine reachable_of_forall_adj_reachable (fun x y hxy => ?_) h
      rcases hxy with hxy | hxy
      · exact Adj.reachable (Or.inl hxy)
      · rw [lighter_adj] at hxy
        rcases relKruskalMax_adj.mp (hHM hxy.1) with hTxy | ⟨-, hr⟩
        · exact Adj.reachable (Or.inr (lighter_adj.mpr ⟨hTxy, hxy.2⟩))
        · exact hr.mono (sup_le_sup_left (lighter_mono_right _ hxy.2.le) K)
    ext u v
    constructor
    · rintro ⟨huv, hnr⟩
      by_contra hTuv
      rcases relKruskalMax_adj.mp (hHM huv) with h | ⟨-, hr⟩
      · exact hTuv h
      · exact hnr (hr.mono (sup_le_sup_left (lighter_mono_left hTH _) K))
    · intro hTuv
      exact ⟨hTH hTuv, fun hr => not_reachable_lighter_of_isRelForest hT hTuv (key _ _ _ hr)⟩

/-- Graphs defined by a greedy recursion are unique: if each edge `uv` of `T₁` (resp. `T₂`) is
decided by the same rule `Φ` from the edges of `T₁` (resp. `T₂`) lighter than `uv`, then
`T₁ = T₂`. -/
theorem eq_of_forall_adj_iff_lighter {T₁ T₂ : SimpleGraph V} (Φ : SimpleGraph V → V → V → Prop)
    (h₁ : ∀ u v, T₁.Adj u v ↔ Φ (lighter w T₁ (w s(u, v))) u v)
    (h₂ : ∀ u v, T₂.Adj u v ↔ Φ (lighter w T₂ (w s(u, v))) u v) : T₁ = T₂ := by
  have key : ∀ n, lighter w T₁ n = lighter w T₂ n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      ext u v
      rw [lighter_adj, lighter_adj]
      refine ⟨fun ⟨h, hn⟩ => ⟨(h₂ u v).mpr ?_, hn⟩, fun ⟨h, hn⟩ => ⟨(h₁ u v).mpr ?_, hn⟩⟩
      · rw [← ih _ hn]
        exact (h₁ u v).mp h
      · rw [ih _ hn]
        exact (h₂ u v).mp h
  ext u v
  rw [h₁, h₂, key]

end RelKruskal

section Lex

variable {V : Type*} [LinearOrder V]

/-- The lexicographic key of an edge `ij`: the pair `(min(i, j), max(i, j))` in the
lexicographic order. -/
def lexKey (e : Sym2 V) : V ×ₗ V := toLex (e.inf, e.sup)

theorem lexKey_injective : Function.Injective (lexKey (V := V)) := by
  intro e e' h
  have h' : (e.inf, e.sup) = (e'.inf, e'.sup) := toLex.injective h
  simp only [Prod.mk.injEq] at h'
  exact Sym2.inf_eq_inf_and_sup_eq_sup.mp h'

variable [Fintype V]

/-- The rank of an edge in the lexicographic order of edges: the number of edges with a
smaller lexicographic key. It is an injective weight inducing the lexicographic order
(`MultipoleBKT.lexRank_lt_lexRank_iff`). -/
def lexRank (e : Sym2 V) : ℕ := #{e' | lexKey e' < lexKey e}

theorem lexRank_lt_lexRank_iff {e e' : Sym2 V} :
    lexRank e < lexRank e' ↔ lexKey e < lexKey e' := by
  constructor
  · intro h
    by_contra h'
    rw [not_lt] at h'
    refine absurd h (not_lt.mpr (card_le_card fun x hx => ?_))
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact hx.trans_le h'
  · intro h
    refine card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
    · simp only [mem_filter, mem_univ, true_and] at hx ⊢
      exact hx.trans h
    · have he : e ∈ ({e'' | lexKey e'' < lexKey e'} : Finset (Sym2 V)) := by simp [h]
      have := hsub he
      simp at this

theorem lexRank_injective : Function.Injective (lexRank (V := V)) := by
  intro e e' h
  rcases lt_trichotomy (lexKey e) (lexKey e') with h' | h' | h'
  · exact absurd h (lexRank_lt_lexRank_iff.mpr h').ne
  · exact lexKey_injective h'
  · exact absurd h (lexRank_lt_lexRank_iff.mpr h').ne'

end Lex

section Forest

variable {V : Type*}

/-- Adding one edge `uv` to a graph `G`: if `a` and `b` become joined, they were joined in `G`,
or `a` was joined to one endpoint of `uv` and `b` to the other. -/
theorem reachable_sup_edge {G : SimpleGraph V} {u v a b : V}
    (h : (G ⊔ edge u v).Reachable a b) :
    G.Reachable a b ∨ (G.Reachable a u ∧ G.Reachable v b) ∨
      (G.Reachable a v ∧ G.Reachable u b) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Or.inl (Reachable.refl _)
  | @cons a c b hadj _ ih =>
    rcases hadj with hadj | hadj
    · rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (hadj.reachable.trans h)
      · exact Or.inr (Or.inl ⟨hadj.reachable.trans h1, h2⟩)
      · exact Or.inr (Or.inr ⟨hadj.reachable.trans h1, h2⟩)
    · rw [edge_adj] at hadj
      rcases hadj.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases ih with h | ⟨h1, h2⟩ | ⟨-, h2⟩
        · exact Or.inr (Or.inl ⟨Reachable.refl _, h⟩)
        · exact Or.inl (h1.symm.trans h2)
        · exact Or.inl h2
      · rcases ih with h | ⟨-, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr (Or.inr ⟨Reachable.refl _, h⟩)
        · exact Or.inl h2
        · exact Or.inl (h1.symm.trans h2)

/-- A subgraph of a relative forest is a relative forest. -/
theorem IsRelForest.mono {K F T : SimpleGraph V} (hT : IsRelForest K T) (hFT : F ≤ T) :
    IsRelForest K F := fun u v huv hr =>
  hT u v (hFT huv) (hr.mono (sup_le_sup_left (deleteEdges_mono hFT) K))

/-- Adding to a relative forest `F` an edge `uv` outside `F ∪ K` gives a relative forest iff
the endpoints of `uv` are not already joined in `K ∪ F`. -/
theorem isRelForest_sup_edge_iff {K F : SimpleGraph V} (hF : IsRelForest K F) {u v : V}
    (huv : u ≠ v) (hFuv : ¬ F.Adj u v) (hKuv : ¬ K.Adj u v) :
    IsRelForest K (F ⊔ edge u v) ↔ ¬ (K ⊔ F).Reachable u v := by
  have hdel : (F ⊔ edge u v).deleteEdges {s(u, v)} = F := by
    ext a b
    rw [deleteEdges_adj, sup_adj, edge_adj, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h | ⟨h, -⟩, hne⟩
      · exact h
      · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd rfl hne
        · exact absurd Sym2.eq_swap hne
    · intro h
      refine ⟨Or.inl h, fun heq => ?_⟩
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hFuv h
      · exact hFuv h.symm
  constructor
  · intro h hr
    refine h u v (Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩)) ?_
    rwa [hdel]
  · intro hnr a b hab hr
    by_cases he : s(a, b) = s(u, v)
    · rw [he, hdel] at hr
      rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hnr hr
      · exact hnr hr.symm
    · have habF : F.Adj a b := by
        rcases hab with hab | hab
        · exact hab
        · rw [edge_adj] at hab
          rcases hab.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact absurd rfl he
          · exact absurd Sym2.eq_swap he
      set G := K ⊔ F.deleteEdges {s(a, b)}
      have hle : K ⊔ (F ⊔ edge u v).deleteEdges {s(a, b)} ≤ G ⊔ edge u v := by
        intro x y hxy
        rcases hxy with hxy | hxy
        · exact Or.inl (Or.inl hxy)
        · rw [deleteEdges_adj, sup_adj] at hxy
          rcases hxy with ⟨hxy | hxy, hne⟩
          · exact Or.inl (Or.inr (deleteEdges_adj.mpr ⟨hxy, hne⟩))
          · exact Or.inr hxy
      have hGF : G ≤ K ⊔ F := sup_le_sup_left (deleteEdges_le _) K
      have hab' : (K ⊔ F).Reachable a b := (show (K ⊔ F).Adj a b from Or.inr habF).reachable
      rcases reachable_sup_edge (hr.mono hle) with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hF a b habF h
      · exact hnr ((h1.mono hGF).symm.trans (hab'.trans (h2.mono hGF).symm))
      · exact hnr ((h2.mono hGF).trans (hab'.symm.trans (h1.mono hGF)))

end Forest

section QuotientPath

variable {V β : Type*} {b : V → β}

/-- Let `T` be an edge set whose quotient by the blocks of `b` is a tree with one representative
per quotient edge, and `F ⊆ T`. Two vertices `u`, `v` are joined by same-block edges and edges
of `F` iff every edge of `T` whose quotient edge lies on the path from `[u]` to `[v]` in the
quotient tree belongs to `F`. -/
theorem reachable_sup_sameBlockGraph_iff_forall_path {T F : SimpleGraph V}
    (hT : (blockQuotient b T).IsTree) (hu : HasUniqueReps b T) (hFT : F ≤ T) {u v : V} :
    (F ⊔ sameBlockGraph b).Reachable u v ↔
      ∀ p : (blockQuotient b T).Walk (b u) (b v), p.IsPath →
        ∀ a c, T.Adj a c → s(b a, b c) ∈ p.edges → F.Adj a c := by
  classical
  constructor
  · intro hr p hp a c hac hmem
    by_contra hF
    have hQ : (blockQuotient b T).Adj (b a) (b c) := p.adj_of_mem_edges hmem
    have hle : blockQuotient b F ≤ (blockQuotient b T).deleteEdges {s(b a, b c)} := by
      intro B B' h
      obtain ⟨hne, x, y, rfl, rfl, hxy⟩ := blockQuotient_adj.mp h
      refine deleteEdges_adj.mpr ⟨blockQuotient_adj_of_adj (hFT hxy) hne, fun heq => hF ?_⟩
      rw [Set.mem_singleton_iff] at heq
      rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := (hu _ _ hQ).unique (y₁ := (x, y)) (y₂ := (a, c)) ⟨h1, h2, hFT hxy⟩
          ⟨rfl, rfl, hac⟩
        simp only [Prod.mk.injEq] at this
        rw [← this.1, ← this.2]
        exact hxy
      · have := (hu _ _ hQ).unique (y₁ := (y, x)) (y₂ := (a, c)) ⟨h2, h1, (hFT hxy).symm⟩
          ⟨rfl, rfl, hac⟩
        simp only [Prod.mk.injEq] at this
        rw [← this.1, ← this.2]
        exact hxy.symm
    obtain ⟨q, hq⟩ :=
      reachable_deleteEdges_iff_exists_walk.mp ((reachable_blockQuotient_of_reachable hr).mono hle)
    have hpq : (⟨p, hp⟩ : (blockQuotient b T).Path _ _) = q.toPath :=
      (hT.isAcyclic.subsingleton_path _ _).elim _ _
    have hpq' : p = q.toPath.1 := congrArg Subtype.val hpq
    rw [hpq'] at hmem
    exact hq (Walk.edges_toPath_subset_edges q hmem)
  · intro h
    obtain ⟨p⟩ := hT.connected.preconnected (b u) (b v)
    have hp : ∀ e ∈ p.toPath.1.edges,
        e ∈ (blockQuotient b F).edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | h B B' =>
        have hQ := Walk.adj_of_mem_edges _ he
        obtain ⟨hne, a, c, rfl, rfl, hac⟩ := blockQuotient_adj.mp hQ
        exact blockQuotient_adj_of_adj (h p.toPath.1 p.toPath.2 a c hac he) hne
    exact reachable_of_reachable_blockQuotient ⟨Walk.transfer _ _ hp⟩ rfl rfl

end QuotientPath

section Subpartition

variable {X : Finset (Finset ℕ)}

variable (X) in
/-- The relative Kruskal map `𝒯^KA_X` (Definition 4.50(1)), for the
lexicographic order on the edges: the edges `uv` of `H` whose endpoints are not joined by
`ℰ^intra(X)` together with the edges of `H` lexicographically smaller than `uv`. On `𝖤_0^X` it
is the greedy procedure of the paper (`MultipoleBKT.kruskalTree_adj_iff_not_hasRelCycle`) and
takes values in `𝖳_0^X` (`MultipoleBKT.IsRelConnected₀.isRelTree₀_kruskalTree`). -/
def kruskalTree (H : SimpleGraph (X.biUnion id)) : SimpleGraph (X.biUnion id) :=
  relKruskal (intraEdges X) lexRank H

variable (X) in
/-- The set `𝓔^KA_max(X, T)` (Definition 4.50(2)): the edges of `T`, and the
edges `uv ∈ ℰ^inter(X)` whose endpoints are joined by `ℰ^intra(X)` together with the edges of
`T` lexicographically smaller than `uv`. For `T ∈ 𝖳_0^X` it is the greatest `H ∈ 𝖤_0^X` with
`𝒯^KA_X(H) = T` (`MultipoleBKT.isGreatest_kruskalMax`). -/
def kruskalMax (T : SimpleGraph (X.biUnion id)) : SimpleGraph (X.biUnion id) :=
  relKruskalMax (intraEdges X) lexRank (interEdges X) T

theorem kruskalTree_le (H : SimpleGraph (X.biUnion id)) : kruskalTree X H ≤ H :=
  relKruskal_le H

theorem le_kruskalMax (T : SimpleGraph (X.biUnion id)) : T ≤ kruskalMax X T :=
  le_relKruskalMax _ T

theorem kruskalMax_le_interEdges {T : SimpleGraph (X.biUnion id)} (hT : T ≤ interEdges X) :
    kruskalMax X T ≤ interEdges X :=
  (relKruskalMax_le _ T).trans (sup_le hT le_rfl)

/-- The greedy description of `𝒯^KA_X` (Definition 4.50(1)): an edge `uv` of `H` is kept iff
its endpoints are not joined by `ℰ^intra(X)` and the previously kept edges, i.e. the kept edges
lexicographically smaller than `uv`. -/
theorem kruskalTree_adj_iff {H : SimpleGraph (X.biUnion id)} {u v : X.biUnion id} :
    (kruskalTree X H).Adj u v ↔ H.Adj u v ∧
      ¬ (intraEdges X ⊔ lighter lexRank (kruskalTree X H) (lexRank s(u, v))).Reachable u v :=
  relKruskal_adj_iff

/-- The relative Kruskal forest is a forest relative to `ℰ^intra(X)`. -/
theorem isRelForest_kruskalTree (hX : IsSubpartition X) {H : SimpleGraph (X.biUnion id)}
    (hH : H ≤ interEdges X) : IsRelForest (intraEdges X) (kruskalTree X H) :=
  relKruskal_isRelForest lexRank_injective fun _ _ h => not_intraEdges_adj_of_le hX hH h

/-- The greedy procedure of Definition 4.50(1), literally: selecting the edges of
`H ⊆ ℰ^inter(X)` in increasing lexicographic order, an edge `uv` is kept iff it does not form a
cycle relative to `X` with the previously kept edges. -/
theorem kruskalTree_adj_iff_not_hasRelCycle (hX : IsSubpartition X)
    {H : SimpleGraph (X.biUnion id)} (hH : H ≤ interEdges X) {u v : X.biUnion id} :
    (kruskalTree X H).Adj u v ↔ H.Adj u v ∧
      ¬ HasRelCycle X (lighter lexRank (kruskalTree X H) (lexRank s(u, v)) ⊔ edge u v) := by
  rw [kruskalTree_adj_iff]
  refine and_congr_right fun huv => ?_
  set F := lighter lexRank (kruskalTree X H) (lexRank s(u, v))
  have hFT : F ≤ kruskalTree X H := lighter_le _ _
  have hFle : F ⊔ edge u v ≤ interEdges X := by
    refine sup_le (hFT.trans ((kruskalTree_le H).trans hH)) fun a b hab => ?_
    rw [edge_adj] at hab
    rcases hab.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hH huv
    · exact (hH huv).symm
  have hFuv : ¬ F.Adj u v := fun h => lt_irrefl _ (lighter_adj.mp h).2
  rw [hasRelCycle_iff_not_isRelForest hX hFle, not_not,
    isRelForest_sup_edge_iff ((isRelForest_kruskalTree hX hH).mono hFT) huv.ne hFuv
      (not_intraEdges_adj_of_le hX hH huv)]

/-- `𝒯^KA_X(H)` is the unique graph produced by the greedy procedure of Definition 4.50(1):
`T' = 𝒯^KA_X(H)` iff each edge `uv` of `H` is kept in `T'` exactly when it does not form a cycle
relative to `X` with the edges of `T'` lexicographically smaller than `uv`. -/
theorem eq_kruskalTree_iff (hX : IsSubpartition X) {H T' : SimpleGraph (X.biUnion id)}
    (hH : H ≤ interEdges X) :
    T' = kruskalTree X H ↔ ∀ u v, T'.Adj u v ↔
      H.Adj u v ∧ ¬ HasRelCycle X (lighter lexRank T' (lexRank s(u, v)) ⊔ edge u v) := by
  constructor
  · rintro rfl u v
    exact kruskalTree_adj_iff_not_hasRelCycle hX hH
  · intro h
    exact eq_of_forall_adj_iff_lighter (fun F u v => H.Adj u v ∧ ¬ HasRelCycle X (F ⊔ edge u v))
      h fun u v => kruskalTree_adj_iff_not_hasRelCycle hX hH

/-- `𝒯^KA_X` maps `𝖤_0^X` into `𝖳_0^X`. -/
theorem IsRelConnected₀.isRelTree₀_kruskalTree (hX : IsSubpartition X)
    {H : SimpleGraph (X.biUnion id)} (hH : IsRelConnected₀ X H) :
    IsRelTree₀ X (kruskalTree X H) := by
  obtain ⟨hle, hconn⟩ := (isRelConnected₀_iff hX).mp hH
  refine (isRelTree₀_iff hX).mpr ⟨(kruskalTree_le H).trans hle, ?_,
    isRelForest_kruskalTree hX hle⟩
  have : Nonempty (X.biUnion id) := hconn.nonempty
  refine ⟨fun u v => ?_⟩
  rw [sup_comm] at hconn ⊢
  exact reachable_relKruskal (hconn.preconnected u v)

/-- The fibres of `𝒯^KA_X` are intervals: for `T ∈ 𝖳_0^X` and `H ⊆ ℰ^inter(X)`,
`𝒯^KA_X(H) = T` iff `T ≤ H ≤ 𝓔^KA_max(X, T)`. -/
theorem kruskalTree_eq_iff (hX : IsSubpartition X) {T H : SimpleGraph (X.biUnion id)}
    (hT : IsRelTree₀ X T) (hH : H ≤ interEdges X) :
    kruskalTree X H = T ↔ T ≤ H ∧ H ≤ kruskalMax X T :=
  relKruskal_eq_iff ((isRelTree₀_iff hX).mp hT).2.2 hH

/-- The characterization used in the proof of Lemma 4.51: for `H ∈ 𝖤_0^X` and
`T ∈ 𝖳_0^X`, `𝒯^KA_X(H) = T` iff `T ⊆ H` and `H ∖ T ⊆ 𝓔^KA_max(X, T) ∖ T`. -/
theorem kruskalTree_eq_iff_sdiff (hX : IsSubpartition X) {T H : SimpleGraph (X.biUnion id)}
    (hT : IsRelTree₀ X T) (hH : IsRelConnected₀ X H) :
    kruskalTree X H = T ↔ T.edgeSet ⊆ H.edgeSet ∧
      H.edgeSet \ T.edgeSet ⊆ (kruskalMax X T).edgeSet \ T.edgeSet := by
  rw [kruskalTree_eq_iff hX hT hH.le_interEdges, ← edgeSet_sdiff, ← edgeSet_sdiff,
    edgeSet_subset_edgeSet, edgeSet_subset_edgeSet]
  refine and_congr_right fun _ => ⟨fun h => sdiff_le_sdiff_right h, fun h => ?_⟩
  have := sdiff_le_iff.mp (h.trans sdiff_le)
  rwa [sup_eq_right.mpr (le_kruskalMax T)] at this

/-- For `T ∈ 𝖳_0^X`, the fibre `{H ∈ 𝖤_0^X : 𝒯^KA_X(H) = T}` is the interval
`[T, 𝓔^KA_max(X, T)]`. -/
theorem isRelConnected₀_and_kruskalTree_eq_iff (hX : IsSubpartition X)
    {T H : SimpleGraph (X.biUnion id)} (hT : IsRelTree₀ X T) :
    IsRelConnected₀ X H ∧ kruskalTree X H = T ↔ T ≤ H ∧ H ≤ kruskalMax X T := by
  constructor
  · rintro ⟨hH, heq⟩
    exact (kruskalTree_eq_iff hX hT hH.le_interEdges).mp heq
  · rintro ⟨hTH, hHM⟩
    have hHle : H ≤ interEdges X := hHM.trans (kruskalMax_le_interEdges hT.le_interEdges)
    obtain ⟨-, hconn, -⟩ := (isRelTree₀_iff hX).mp hT
    refine ⟨(isRelConnected₀_iff hX).mpr ⟨hHle, hconn.mono (sup_le_sup_right hTH _)⟩, ?_⟩
    exact (kruskalTree_eq_iff hX hT hHle).mpr ⟨hTH, hHM⟩

/-- `𝓔^KA_max(X, T)` is the greatest element of the fibre of `𝒯^KA_X` over `T ∈ 𝖳_0^X`
(Definition 4.50(2)). -/
theorem isGreatest_kruskalMax (hX : IsSubpartition X) {T : SimpleGraph (X.biUnion id)}
    (hT : IsRelTree₀ X T) :
    IsGreatest {H | IsRelConnected₀ X H ∧ kruskalTree X H = T} (kruskalMax X T) := by
  refine ⟨(isRelConnected₀_and_kruskalTree_eq_iff hX hT).mpr ⟨le_kruskalMax T, le_rfl⟩, ?_⟩
  rintro H hH
  exact ((isRelConnected₀_and_kruskalTree_eq_iff hX hT).mp hH).2

/-- The construction of `𝓔^KA_max(X, T)` in Definition 4.50(2): for
`T ∈ 𝖳_0^X`, an edge `uv ∈ ℰ^inter(X) ∖ T` belongs to `𝓔^KA_max(X, T)` iff it is
lexicographically larger than every edge of `T` on the path of the quotient tree `(V_X, T)/X`
between the blocks of `u` and `v` (each quotient edge being identified with the unique edge of
`T` it comes from). -/
theorem kruskalMax_adj_iff_path (hX : IsSubpartition X) {T : SimpleGraph (X.biUnion id)}
    (hT : IsRelTree₀ X T) {u v : X.biUnion id} (huv : (interEdges X).Adj u v)
    (hTuv : ¬ T.Adj u v) :
    (kruskalMax X T).Adj u v ↔
      ∀ p : (quotientGraph X T).Walk (blockOf hX u) (blockOf hX v), p.IsPath →
        ∀ a c, T.Adj a c → s(blockOf hX a, blockOf hX c) ∈ p.edges →
          lexKey s(a, c) < lexKey s(u, v) := by
  obtain ⟨hle, -, hF⟩ := (isRelTree₀_iff hX).mp hT
  have htree := hT.isTree_quotientGraph hX
  rw [interEdges_eq hX] at hle
  rw [intraEdges_eq hX] at hF
  have hu := ((isRelForest_iff hle).mp hF).2
  rw [quotientGraph_eq hX] at htree ⊢
  rw [kruskalMax, relKruskalMax_adj, or_iff_right hTuv, and_iff_right huv, intraEdges_eq hX,
    sup_comm, reachable_sup_sameBlockGraph_iff_forall_path htree hu (lighter_le _ _)]
  simp only [lighter_adj, lexRank_lt_lexRank_iff]
  exact forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun hac => forall_congr' fun _ => and_iff_right hac

/-- For a single block, `𝒯^KA_X(∅) = 𝓔^KA_max(X, ∅) = ∅` (Definition 4.50). -/
theorem kruskalTree_bot_and_kruskalMax_bot_of_card_eq_one (h : X.card = 1) :
    kruskalTree X ⊥ = ⊥ ∧ kruskalMax X ⊥ = ⊥ := by
  refine ⟨le_bot_iff.mp (kruskalTree_le ⊥), le_bot_iff.mp ?_⟩
  refine (kruskalMax_le_interEdges bot_le).trans ?_
  rw [interEdges_eq_bot_of_card_eq_one h]

end Subpartition

section Interval

variable {V : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommSemiring R]

open scoped Classical in
/-- Sum over the interval `[T, M]` of graphs: `∑_{T ≤ H ≤ M} ∏_{e ∈ H} c_e
= ∏_{e ∈ T} c_e ∏_{e ∈ M ∖ T} (1 + c_e)`. -/
theorem sum_interval_prod_edgeFinset {T M : SimpleGraph V} (hTM : T ≤ M) (c : Sym2 V → R) :
    ∑ H ∈ (univ : Finset (SimpleGraph V)).filter (fun H => T ≤ H ∧ H ≤ M),
      ∏ e ∈ H.edgeFinset, c e =
    (∏ e ∈ T.edgeFinset, c e) * ∏ e ∈ M.edgeFinset \ T.edgeFinset, (1 + c e) := by
  rw [prod_one_add, mul_sum]
  refine sum_nbij' (fun H => H.edgeFinset \ T.edgeFinset)
    (fun S => fromEdgeSet (T.edgeSet ∪ (S : Set (Sym2 V)))) ?_ ?_ ?_ ?_ ?_
  · intro H hH
    simp only [mem_filter, mem_univ, true_and] at hH
    exact mem_powerset.mpr (sdiff_subset_sdiff (edgeFinset_mono hH.2) le_rfl)
  · intro S hS
    rw [mem_powerset] at hS
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro a b hab
      rw [fromEdgeSet_adj]
      exact ⟨Or.inl hab, hab.ne⟩
    · intro a b hab
      rw [fromEdgeSet_adj] at hab
      rcases hab.1 with h | h
      · exact hTM h
      · have := hS h
        rw [mem_sdiff, mem_edgeFinset] at this
        exact this.1
  · intro H hH
    simp only [mem_filter, mem_univ, true_and] at hH
    rw [← edgeSet_inj, edgeSet_fromEdgeSet]
    ext e
    simp only [coe_sdiff, coe_edgeFinset, Set.mem_sdiff, Set.mem_union, Sym2.mem_diagSet]
    constructor
    · rintro ⟨h | h, -⟩
      · exact edgeSet_mono hH.1 h
      · exact h.1
    · intro h
      refine ⟨?_, fun hd => H.not_isDiag_of_mem_edgeSet h hd⟩
      by_cases hT : e ∈ T.edgeSet
      · exact Or.inl hT
      · exact Or.inr ⟨h, hT⟩
  · intro S hS
    rw [mem_powerset] at hS
    ext e
    simp only [mem_sdiff, mem_edgeFinset, edgeSet_fromEdgeSet, Set.mem_sdiff, Set.mem_union,
      mem_coe, Sym2.mem_diagSet]
    constructor
    · rintro ⟨⟨h | h, -⟩, hT⟩
      · exact absurd h hT
      · exact h
    · intro h
      have := hS h
      rw [mem_sdiff, mem_edgeFinset] at this
      exact ⟨⟨Or.inr h, fun hd => M.not_isDiag_of_mem_edgeSet this.1 hd⟩,
        fun hT => this.2 (mem_edgeFinset.mpr hT)⟩
  · intro H hH
    simp only [mem_filter, mem_univ, true_and] at hH
    rw [← prod_union disjoint_sdiff, union_sdiff_of_subset (edgeFinset_mono hH.1)]

end Interval

section Penrose

variable {X : Finset (Finset ℕ)}

open scoped Classical in
/-- **Penrose resummation**, Lemma 4.51 (equation (4.86)): for a
subpartition `X` and weights `c_ij` on the edges,
`∑_{H ∈ 𝖤_0^X} ∏_{ij ∈ H} c_ij`
`= ∑_{T ∈ 𝖳_0^X} ∏_{ij ∈ T} c_ij ∏_{ij ∈ 𝓔^KA_max(X,T) ∖ T} (1 + c_ij)`.
The paper takes `c_ij ∈ ℝ` for `ij ∈ ℰ^inter(X)`; here `c` is defined on all edges (its values
off `ℰ^inter(X)` do not enter) and takes values in any commutative semiring. -/
theorem penrose (hX : IsSubpartition X) {R : Type*} [CommSemiring R]
    (c : Sym2 (X.biUnion id) → R) :
    ∑ H ∈ relConnected₀ X, ∏ e ∈ H.edgeFinset, c e =
      ∑ T ∈ relTrees₀ X, (∏ e ∈ T.edgeFinset, c e) *
        ∏ e ∈ (kruskalMax X T).edgeFinset \ T.edgeFinset, (1 + c e) := by
  have hmaps : ∀ H ∈ relConnected₀ X, kruskalTree X H ∈ relTrees₀ X := fun H hH =>
    mem_relTrees₀.mpr ((mem_relConnected₀.mp hH).isRelTree₀_kruskalTree hX)
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun T hT => ?_
  rw [← sum_interval_prod_edgeFinset (le_kruskalMax T) c]
  refine sum_congr ?_ fun _ _ => rfl
  ext H
  simp only [relConnected₀, mem_filter, mem_univ, true_and]
  exact isRelConnected₀_and_kruskalTree_eq_iff hX (mem_relTrees₀.mp hT)

open scoped Classical in
/-- Penrose resummation for nonnegative weights (as used in the proof of Lemma 4.54): if
`c_ij ≥ 0` on `ℰ^inter(X)`, then
`∑_{H ∈ 𝖤_0^X} ∏_{ij ∈ H} c_ij ≤ ∑_{T ∈ 𝖳_0^X} ∏_{ij ∈ T} c_ij ∏_{ij ∈ ℰ^inter(X)} (1 + c_ij)`. -/
theorem penrose_le (hX : IsSubpartition X) (c : Sym2 (X.biUnion id) → ℝ)
    (hc : ∀ e ∈ (interEdges X).edgeSet, 0 ≤ c e) :
    ∑ H ∈ relConnected₀ X, ∏ e ∈ H.edgeFinset, c e ≤
      ∑ T ∈ relTrees₀ X, (∏ e ∈ T.edgeFinset, c e) *
        ∏ e ∈ (interEdges X).edgeFinset, (1 + c e) := by
  rw [penrose hX c]
  refine sum_le_sum fun T hT => ?_
  have hTle := (mem_relTrees₀.mp hT).le_interEdges
  have hMle := kruskalMax_le_interEdges hTle
  refine mul_le_mul_of_nonneg_left ?_
    (prod_nonneg fun e he => hc e (edgeSet_mono hTle (mem_edgeFinset.mp he)))
  refine prod_le_prod_of_subset_of_one_le₀ (sdiff_subset.trans (edgeFinset_mono hMle)) ?_ ?_
  · intro e he
    have := hc e (edgeSet_mono hMle (mem_edgeFinset.mp (mem_sdiff.mp he).1))
    linarith
  · intro e he _
    have := hc e (mem_edgeFinset.mp he)
    linarith

open scoped Classical in
/-- Penrose resummation for weights with `|1 + c_ij| ≤ 1` on `ℰ^inter(X)` (as used in Section 4 with
`c_ij = -𝟙_{𝓑_ij}`, equation (4.87)):
`|∑_{H ∈ 𝖤_0^X} ∏_{ij ∈ H} c_ij| ≤ ∑_{T ∈ 𝖳_0^X} ∏_{ij ∈ T} |c_ij|`. -/
theorem abs_penrose_le (hX : IsSubpartition X) (c : Sym2 (X.biUnion id) → ℝ)
    (hc : ∀ e ∈ (interEdges X).edgeSet, |1 + c e| ≤ 1) :
    |∑ H ∈ relConnected₀ X, ∏ e ∈ H.edgeFinset, c e| ≤
      ∑ T ∈ relTrees₀ X, ∏ e ∈ T.edgeFinset, |c e| := by
  rw [penrose hX c]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun T hT => ?_)
  have hMle := kruskalMax_le_interEdges (mem_relTrees₀.mp hT).le_interEdges
  rw [abs_mul, abs_prod, abs_prod]
  refine mul_le_of_le_one_right (prod_nonneg fun _ _ => abs_nonneg _)
    (prod_le_one₀ (fun _ _ => abs_nonneg _) fun e he => hc e ?_)
  exact edgeSet_mono hMle (mem_edgeFinset.mp (mem_sdiff.mp he).1)

end Penrose

section Product

variable {V : Type*} [Fintype V] [LinearOrder V] {R : Type*} [CommMonoid R]

open scoped Classical in
/-- Products over the pairs `i < j` of adjacent vertices (the form of the frozen
`MultipoleBKT.multipoleActivity`) are products over the edges, with the weight
`c_{ij} = f(min(i, j), max(i, j))`. -/
theorem prod_prod_ite_lt_adj (E : SimpleGraph V) (f : V → V → R) :
    ∏ i : V, ∏ j : V, (if i < j ∧ E.Adj i j then f i j else 1) =
      ∏ e ∈ E.edgeFinset, f e.inf e.sup := by
  rw [← prod_product' (f := fun i j => if i < j ∧ E.Adj i j then f i j else 1),
    univ_product_univ, ← prod_filter]
  refine prod_nbij' (fun p => s(p.1, p.2)) (fun e => (e.inf, e.sup)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    exact mem_edgeFinset.mpr hp.2
  · intro e he
    rw [mem_edgeFinset] at he
    simp only [mem_filter, mem_univ, true_and]
    induction e using Sym2.ind with
    | h a b =>
      rw [mem_edgeSet] at he
      simp only [Sym2.inf_mk, Sym2.sup_mk]
      refine ⟨min_lt_max.mpr he.ne, ?_⟩
      rcases le_total a b with hab | hab
      · rwa [min_eq_left hab, max_eq_right hab]
      · rw [min_eq_right hab, max_eq_left hab]
        exact he.symm
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    simp [min_eq_left hp.1.le, max_eq_right hp.1.le]
  · intro e _
    induction e using Sym2.ind with
    | h a b =>
      simp only [Sym2.inf_mk, Sym2.sup_mk]
      rcases le_total a b with hab | hab
      · rw [min_eq_left hab, max_eq_right hab]
      · rw [min_eq_right hab, max_eq_left hab, Sym2.eq_swap]
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    simp [min_eq_left hp.1.le, max_eq_right hp.1.le]

end Product

end MultipoleBKT

end
