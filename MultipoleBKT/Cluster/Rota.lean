/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Cluster.Ursell
public import MultipoleBKT.Cluster.RouteCounts.PenroseProduct

/-!
# Rota's bound on the Ursell function

We prove Rota's theorem (equation (4.87)): for every finite graph `G`,

  `|I(G)| ≤ #{spanning trees of G}`

(`MultipoleBKT.abs_ursell_le_card_isTree`).

The paper deduces it from the Penrose resummation with Kruskal's partition scheme. We follow
the same route. Fix injective edge weights `w`. Kruskal's forest of a graph `H`
(`MultipoleBKT.kruskalForest`) keeps the edges of `H` whose endpoints are not joined by
strictly lighter edges of `H`. For connected `H` it is a spanning tree
(`MultipoleBKT.kruskalForest_isTree`), and the graphs `H` with a given Kruskal tree `T` form an
interval `[T, T ∪ R(T)]` (`MultipoleBKT.kruskalForest_eq_of_le`). Grouping the sum defining
`I(G)` by the Kruskal tree, each fiber is evaluated by the Penrose product formula
`sum_kruskal_fiber_eq_prod`. Its optional-edge product consists of factors `1 - 1`,
so equals zero if there is an optional edge and one otherwise.
-/

@[expose] public section

namespace MultipoleBKT

open Finset SimpleGraph

variable {V : Type*}

section Kruskal

variable (w : Sym2 V → ℕ)

/-- The subgraph of `H` formed by its edges of weight `< n`. -/
def lighter (H : SimpleGraph V) (n : ℕ) : SimpleGraph V :=
  H.deleteEdges {f | n ≤ w f}

/-- Kruskal's spanning forest of `H` for the edge weights `w`: the edges `uv` of `H` such that
`u` and `v` are not joined by a path of edges of `H` strictly lighter than `uv`. It is a forest
when `w` is injective (`MultipoleBKT.kruskalForest_isAcyclic`). -/
def kruskalForest (H : SimpleGraph V) : SimpleGraph V where
  Adj u v := H.Adj u v ∧ ¬ (lighter w H (w s(u, v))).Reachable u v
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact fun hr => h.2 hr.symm⟩⟩
  loopless := ⟨fun u h => h.1.ne rfl⟩

variable {w}

theorem lighter_adj {H : SimpleGraph V} {n : ℕ} {u v : V} :
    (lighter w H n).Adj u v ↔ H.Adj u v ∧ w s(u, v) < n := by
  simp [lighter, deleteEdges_adj]

theorem kruskalForest_adj {H : SimpleGraph V} {u v : V} :
    (kruskalForest w H).Adj u v ↔ H.Adj u v ∧ ¬ (lighter w H (w s(u, v))).Reachable u v :=
  Iff.rfl

theorem kruskalForest_le (H : SimpleGraph V) : kruskalForest w H ≤ H :=
  fun _ _ h => h.1

theorem lighter_le (H : SimpleGraph V) (n : ℕ) : lighter w H n ≤ H :=
  deleteEdges_le _

theorem lighter_mono_left {H H' : SimpleGraph V} (h : H ≤ H') (n : ℕ) :
    lighter w H n ≤ lighter w H' n :=
  deleteEdges_mono h

theorem lighter_mono_right (H : SimpleGraph V) {m n : ℕ} (h : m ≤ n) :
    lighter w H m ≤ lighter w H n := fun _ _ hadj => by
  rw [lighter_adj] at hadj ⊢
  exact ⟨hadj.1, hadj.2.trans_le h⟩

/-- Lighter edges of `H` connect what lighter edges of its Kruskal forest connect. -/
theorem reachable_lighter_kruskalForest (H : SimpleGraph V) (n : ℕ) {u v : V}
    (h : (lighter w H n).Reachable u v) :
    (lighter w (kruskalForest w H) n).Reachable u v := by
  induction n using Nat.strong_induction_on generalizing u v with
  | _ n ih =>
    refine reachable_of_forall_adj_reachable (fun x y hxy => ?_) h
    rw [lighter_adj] at hxy
    by_cases hT : (kruskalForest w H).Adj x y
    · exact Adj.reachable (lighter_adj.mpr ⟨hT, hxy.2⟩)
    · have hr : (lighter w H (w s(x, y))).Reachable x y := by
        by_contra hr
        exact hT ⟨hxy.1, hr⟩
      exact (ih _ hxy.2 hr).mono (lighter_mono_right _ hxy.2.le)

/-- The Kruskal forest of `H` has the same connected components as `H`. -/
theorem reachable_kruskalForest {H : SimpleGraph V} {u v : V} (h : H.Reachable u v) :
    (kruskalForest w H).Reachable u v := by
  refine reachable_of_forall_adj_reachable (fun x y hxy => ?_) h
  by_cases hT : (kruskalForest w H).Adj x y
  · exact hT.reachable
  · have hr : (lighter w H (w s(x, y))).Reachable x y := by
      by_contra hr
      exact hT ⟨hxy, hr⟩
    exact (reachable_lighter_kruskalForest H _ hr).mono (lighter_le _ _)

theorem kruskalForest_connected {H : SimpleGraph V} (hH : H.Connected) :
    (kruskalForest w H).Connected :=
  connected_of_forall_adj_reachable hH fun _ _ h => reachable_kruskalForest h.reachable

/-- For injective weights, the Kruskal forest is acyclic: the heaviest edge of a cycle would
have its endpoints joined by the lighter edges of the cycle. -/
theorem kruskalForest_isAcyclic (hw : Function.Injective w) (H : SimpleGraph V) :
    (kruskalForest w H).IsAcyclic := by
  classical
  intro v c hc
  have hne : c.edges.toFinset.Nonempty := by
    obtain ⟨e, he⟩ := c.edges.exists_mem_of_ne_nil (by simp [hc.not_nil])
    exact ⟨e, List.mem_toFinset.mpr he⟩
  obtain ⟨f, hf, hmax⟩ := c.edges.toFinset.exists_max_image w hne
  rw [List.mem_toFinset] at hf
  induction f using Sym2.ind with
  | h x y =>
    have hfT : (kruskalForest w H).Adj x y := c.adj_of_mem_edges hf
    have hc' : ∀ e ∈ c.edges, e ∈ (lighter w (kruskalForest w H) (w s(x, y) + 1)).edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | h a b =>
        rw [mem_edgeSet, lighter_adj]
        exact ⟨c.adj_of_mem_edges he, Nat.lt_succ_of_le (hmax _ (List.mem_toFinset.mpr he))⟩
    have hcyc := (adj_and_reachable_delete_edges_iff_exists_cycle).mpr
      ⟨v, c.transfer _ hc', hc.transfer hc', by simpa using hf⟩
    have hle : (lighter w (kruskalForest w H) (w s(x, y) + 1)).deleteEdges {s(x, y)} ≤
        lighter w H (w s(x, y)) := by
      intro a b hab
      rw [deleteEdges_adj, lighter_adj, Set.mem_singleton_iff] at hab
      obtain ⟨⟨hTab, hlt⟩, hne⟩ := hab
      rw [lighter_adj]
      exact ⟨kruskalForest_le H hTab,
        lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) fun h => hne (hw h)⟩
    exact hfT.2 (hcyc.2.mono hle)

/-- For injective weights, the Kruskal forest of a connected graph is a spanning tree. -/
theorem kruskalForest_isTree (hw : Function.Injective w) {H : SimpleGraph V}
    (hH : H.Connected) : (kruskalForest w H).IsTree :=
  ⟨kruskalForest_connected hH, kruskalForest_isAcyclic hw H⟩

/-- An edge of `H` outside its Kruskal forest `T` has its endpoints joined by edges of `T`
lighter than it. -/
theorem reachable_of_not_kruskalForest_adj {H : SimpleGraph V} {x y : V} (h : H.Adj x y)
    (hT : ¬ (kruskalForest w H).Adj x y) :
    (lighter w (kruskalForest w H) (w s(x, y))).Reachable x y := by
  refine reachable_lighter_kruskalForest H _ ?_
  by_contra hr
  exact hT ⟨h, hr⟩

/-- The fibres of the Kruskal map are intervals: if `T` is the Kruskal forest of some graph,
`T ≤ H'`, and every edge of `H'` outside `T` has its endpoints joined by lighter edges of `T`,
then `T` is the Kruskal forest of `H'`. -/
theorem kruskalForest_eq_of_le {H H' : SimpleGraph V} (hTH' : kruskalForest w H ≤ H')
    (hH' : ∀ x y, H'.Adj x y → ¬ (kruskalForest w H).Adj x y →
      (lighter w (kruskalForest w H) (w s(x, y))).Reachable x y) :
    kruskalForest w H' = kruskalForest w H := by
  set T := kruskalForest w H
  have key : ∀ n u v, (lighter w H' n).Reachable u v → (lighter w T n).Reachable u v := by
    intro n u v h
    refine reachable_of_forall_adj_reachable (fun a b hab => ?_) h
    rw [lighter_adj] at hab
    by_cases hTab : T.Adj a b
    · exact Adj.reachable (lighter_adj.mpr ⟨hTab, hab.2⟩)
    · exact (hH' a b hab.1 hTab).mono (lighter_mono_right _ hab.2.le)
  ext x y
  constructor
  · rintro ⟨hxy, hnr⟩
    by_contra hTxy
    exact hnr ((hH' x y hxy hTxy).mono (lighter_mono_left hTH' _))
  · intro hTxy
    refine ⟨hTH' hTxy, fun hr => ?_⟩
    have hrT := key _ _ _ hr
    exact hTxy.2 (hrT.mono (lighter_mono_left (kruskalForest_le H) _))

end Kruskal

section Rota

variable [Fintype V]

/-- The maximal graph in the Kruskal interval, intersected with the ambient graph `G`.
The optional edges join vertices already connected by lighter edges of `T`. -/
def rotaKruskalMax (w : Sym2 V → ℕ) (G T : SimpleGraph V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ (T.Adj x y ∨ (lighter w T (w s(x, y))).Reachable x y)
  symm := ⟨fun x y h => ⟨h.1.symm, by
    rw [Sym2.eq_swap]
    exact h.2.elim (fun ht => Or.inl ht.symm) (fun hr => Or.inr hr.symm)⟩⟩
  loopless := ⟨fun x h => h.1.ne rfl⟩

open scoped Classical in
/-- Evaluate a nonempty Kruskal fiber by factoring its mandatory edges and expanding
its optional edges. This is the product of `1 - 1` in (4.87). -/
theorem sum_kruskal_fiber_eq_prod [Fintype (SimpleGraph V)] (w : Sym2 V → ℕ) (G H₀ : SimpleGraph V)
    (h₀G : H₀ ≤ G) (h₀c : H₀.Connected) :
    ∑ H ∈ ((univ : Finset (SimpleGraph V)).filter fun H => H ≤ G ∧ H.Connected).filter
        (fun H => kruskalForest w H = kruskalForest w H₀), ((-1 : ℤ) ^ H.edgeFinset.card) =
      (-1 : ℤ) ^ (kruskalForest w H₀).edgeFinset.card *
        ∏ _e ∈ (rotaKruskalMax w G (kruskalForest w H₀)).edgeFinset \
          (kruskalForest w H₀).edgeFinset, (1 + (-1 : ℤ)) := by
  let T := kruskalForest w H₀
  let U := rotaKruskalMax w G T
  have hTG : T ≤ G := (kruskalForest_le H₀).trans h₀G
  have hTU : T ≤ U := fun _ _ h => ⟨hTG h, Or.inl h⟩
  have hTc : T.Connected := kruskalForest_connected h₀c
  have hset : ((univ : Finset (SimpleGraph V)).filter fun H => H ≤ G ∧ H.Connected).filter
      (fun H => kruskalForest w H = T) =
      (univ : Finset (SimpleGraph V)).filter (fun H => T ≤ H ∧ H ≤ U) := by
    ext H
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨hHG, _⟩, hTH⟩
      refine ⟨hTH ▸ kruskalForest_le H, fun x y hxy => ⟨hHG hxy, ?_⟩⟩
      by_cases ht : T.Adj x y
      · exact Or.inl ht
      · right
        rw [← hTH] at ht ⊢
        exact reachable_of_not_kruskalForest_adj hxy ht
    · rintro ⟨hTH, hHU⟩
      refine ⟨⟨fun _ _ h => (hHU h).1, hTc.mono hTH⟩, ?_⟩
      exact kruskalForest_eq_of_le hTH (fun x y hxy ht =>
        ((hHU hxy).2).resolve_left ht)
  rw [hset]
  have hprod := RouteCounts.sum_graph_interval_prod T U hTU (fun _ => (-1 : ℤ))
  simpa only [prod_const] using hprod

/-- Each optional-edge product is zero when nonempty and one when empty. Therefore
its fiber has absolute contribution at most one, as in (4.87). -/
theorem abs_sum_kruskal_fiber_le_one (w : Sym2 V → ℕ) (G T : SimpleGraph V)
    [DecidablePred fun H : SimpleGraph V => H ≤ G ∧ H.Connected]
    [DecidablePred fun H : SimpleGraph V => kruskalForest w H = T] [Fintype (SimpleGraph V)]
    [∀ H : SimpleGraph V, Fintype H.edgeSet] :
    |∑ H ∈ ((univ : Finset (SimpleGraph V)).filter fun H => H ≤ G ∧ H.Connected).filter
        (fun H => kruskalForest w H = T), ((-1 : ℤ) ^ H.edgeFinset.card)| ≤ 1 := by
  classical
  set F := ((univ : Finset (SimpleGraph V)).filter fun H => H ≤ G ∧ H.Connected).filter
    (fun H => kruskalForest w H = T)
  by_cases hF : F.Nonempty
  · obtain ⟨H₀, hH₀⟩ := hF
    obtain ⟨hH₀G, hH₀c⟩ := (mem_filter.mp (mem_filter.mp hH₀).1).2
    have hT := (mem_filter.mp hH₀).2
    have hprod := sum_kruskal_fiber_eq_prod w G H₀ hH₀G hH₀c
    rw [hT] at hprod
    have heq : (∑ H ∈ F, ((-1 : ℤ) ^ H.edgeFinset.card)) =
        (-1 : ℤ) ^ T.edgeFinset.card *
          ∏ _e ∈ (rotaKruskalMax w G T).edgeFinset \ T.edgeFinset, (1 + (-1 : ℤ)) := by
      simp only [F, prod_const, ← Set.ncard_coe_finset, coe_sdiff, coe_edgeFinset] at hprod ⊢
      convert hprod using 1
      apply sum_congr
      · ext H
        simp only [mem_filter]
      · intro H _
        rfl
    rw [heq, abs_mul]
    simp only [abs_pow, abs_neg, abs_one, one_pow, one_mul, add_neg_cancel]
    by_cases hempty : (rotaKruskalMax w G T).edgeFinset \ T.edgeFinset = ∅
    · rw [hempty, prod_empty, abs_one]
    · obtain ⟨e, he⟩ := nonempty_iff_ne_empty.mpr hempty
      rw [prod_eq_zero he rfl, abs_zero]
      exact zero_le_one
  · rw [not_nonempty_iff_eq_empty.mp hF, sum_empty, abs_zero]
    exact zero_le_one

open scoped Classical in
/-- Rota's bound, equation (4.87): `|I(G)|` is at most the number
of spanning trees of `G`. -/
theorem abs_ursell_le_card_isTree (G : SimpleGraph V) :
    |ursell G| ≤ ((univ : Finset (SimpleGraph V)).filter fun T => T ≤ G ∧ T.IsTree).card := by
  obtain ⟨w, hw⟩ := Countable.exists_injective_nat (Sym2 V)
  rw [ursell_eq_sum]
  have hmaps : ∀ H ∈ (univ : Finset (SimpleGraph V)).filter (fun H => H ≤ G ∧ H.Connected),
      kruskalForest w H ∈ (univ : Finset (SimpleGraph V)).filter fun T => T ≤ G ∧ T.IsTree := by
    intro H hH
    simp only [mem_filter, mem_univ, true_and] at hH ⊢
    exact ⟨(kruskalForest_le H).trans hH.1, kruskalForest_isTree hw hH.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  exact sum_le_sum fun T _ => abs_sum_kruskal_fiber_le_one w G T

/-- Rota's bound, equation (4.87): `|I(G)|` is at most the number of spanning trees of `G`
(stated with `Nat.card`, independently of instances). -/
theorem abs_ursell_le_natCard_isTree (G : SimpleGraph V) :
    |ursell G| ≤ Nat.card {T : SimpleGraph V // T ≤ G ∧ T.IsTree} := by
  classical
  have h := abs_ursell_le_card_isTree G
  rwa [Nat.card_eq_fintype_card, Fintype.card_subtype]

end Rota

end MultipoleBKT

end
