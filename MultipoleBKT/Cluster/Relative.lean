/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Cluster.Ursell
public import MultipoleBKT.Frozen.IsSubpartition
public import MultipoleBKT.Frozen.MultipoleActivity

/-!
# Graph notions relative to a subpartition (Definitions 4.9–4.10)

We formalize the graph and partition notions of Definitions 4.9 and 4.10 of the paper. Throughout, `X` is
a subpartition of `ℕ` (`MultipoleBKT.IsSubpartition`), `V_X = ⋃_{S ∈ X} S` is the type
`X.biUnion id`, and edge sets on `V_X` are simple graphs on it, as in the frozen
`MultipoleBKT.multipoleActivity`.

* `MultipoleBKT.interEdges X`, `MultipoleBKT.intraEdges X`: `ℰ^inter(X)` and `ℰ^intra(X)`
  (equations (4.6), (4.7));
* `MultipoleBKT.blockOf hX i`: the block `[i]^X` of a vertex;
* `MultipoleBKT.quotientGraph X E`: the quotient graph `(V_X, E)/X` on the blocks;
* `MultipoleBKT.IsRelConnected`, `MultipoleBKT.relConnected`: `𝖤^X` (the latter is literally
  the edge-set filter of the frozen `multipoleActivity`, `MultipoleBKT.multipoleActivity_eq`);
* `MultipoleBKT.IsRelTree`, `MultipoleBKT.relTrees`: the trees relative to `X`, `𝖳^X`;
* `MultipoleBKT.IsRelConnected₀`, `MultipoleBKT.IsRelTree₀` and the finsets
  `MultipoleBKT.relConnected₀`, `MultipoleBKT.relTrees₀`: `𝖤_0^X` and `𝖳_0^X`, equal to `𝖤^X`
  and `𝖳^X` except that `𝖤_0^{{S}} = 𝖳_0^{{S}} = {∅}`;
* `MultipoleBKT.HasRelCycle X E`: `(V_X, E)` has a cycle relative to `X` (Definition 4.50);
* `MultipoleBKT.coarsen X G`, `MultipoleBKT.restrictBlocks X E`, `MultipoleBKT.quotientMult`,
  `MultipoleBKT.blockDegree`: the coarsening `Coarse_X(X_1, …, X_n)` (for the set
  `G = {X_1, …, X_n}` of groups), `Res(X, E)`, the multiplicities `m_E(S, S')` of the
  multigraph quotient and the block degrees `deg_E(S)`.

The main facts, for a subpartition `X` and `E ⊆ ℰ^inter(X)`:

* `MultipoleBKT.isRelConnected₀_iff`: `E ∈ 𝖤_0^X` iff `(V_X, E ∪ ℰ^intra(X))` is connected, iff
  the quotient graph is connected (`MultipoleBKT.isRelConnected₀_iff_quotient`);
* `MultipoleBKT.isRelTree₀_iff`: `E ∈ 𝖳_0^X` iff the augmented graph is connected and no edge
  of `E` has its endpoints joined in `ℰ^intra(X) ∪ (E ∖ {e})` (`MultipoleBKT.IsRelForest`);
* `MultipoleBKT.isRelTree₀_iff_not_hasRelCycle`: `E ∈ 𝖳_0^X` iff `E ∈ 𝖤_0^X` and `(V_X, E)` has
  no cycle relative to `X`;
* `MultipoleBKT.isRelTree₀_iff_card`: `E ∈ 𝖳_0^X` iff the quotient is a tree on the blocks and
  `|E| = |X| - 1` (the quotient alone being a tree is not enough, see the figure after Definition 4.10);
* `MultipoleBKT.IsRelTree₀.natCard_edgeSet`, `MultipoleBKT.IsRelTree₀.card_edgeFinset`: a
  relative tree has `|X| - 1` edges;
* `MultipoleBKT.isSubpartition_coarsen`, `MultipoleBKT.biUnion_coarsen`: a coarsening is a
  subpartition with the same points.

The proofs go through a generic layer: for a map `b : V → β` (the blocks are its fibres), the
same-block graph `MultipoleBKT.sameBlockGraph b`, the cross-block graph
`MultipoleBKT.crossBlockGraph b` and the quotient `MultipoleBKT.blockQuotient b E`, with
`MultipoleBKT.reachable_sup_sameBlockGraph_iff` (reachability in `E ∪ ℰ^intra` is reachability
of the blocks in the quotient) and `MultipoleBKT.isRelForest_iff` (relative forests are the
edge sets whose quotient is acyclic with one representative per quotient edge).
-/

@[expose] public section

namespace MultipoleBKT

open Finset SimpleGraph

/-- Images of reachable vertices under a map that sends adjacent vertices to reachable ones are
reachable. -/
theorem reachable_comp_of_forall_adj {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}
    (f : V → W) (h : ∀ u v, G.Adj u v → G'.Reachable (f u) (f v)) {u v : V}
    (huv : G.Reachable u v) : G'.Reachable (f u) (f v) := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => exact Reachable.refl _
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

/-- `E` is a forest relative to `K`: no edge `uv` of `E` has its endpoints joined in
`K ∪ (E ∖ {uv})`. For `K = ℰ^intra(X)` and `E ⊆ ℰ^inter(X)` this says that `(V_X, E)` has no
cycle relative to `X` (`MultipoleBKT.hasRelCycle_iff_not_isRelForest`). -/
def IsRelForest {V : Type*} (K E : SimpleGraph V) : Prop :=
  ∀ u v, E.Adj u v → ¬ (K ⊔ E.deleteEdges {s(u, v)}).Reachable u v

section Block

variable {V β : Type*} (b : V → β)

/-- The graph joining two distinct vertices with the same image under `b` (the blocks are the
fibres of `b`). -/
def sameBlockGraph : SimpleGraph V := SimpleGraph.fromRel fun i j => b i = b j

/-- The graph joining two vertices with distinct images under `b`. -/
def crossBlockGraph : SimpleGraph V := SimpleGraph.fromRel fun i j => b i ≠ b j

/-- The quotient of a graph `E` by the blocks of `b`: two distinct blocks are adjacent when
some edge of `E` joins them. -/
def blockQuotient (E : SimpleGraph V) : SimpleGraph β :=
  SimpleGraph.fromRel fun B B' => ∃ i j, b i = B ∧ b j = B' ∧ E.Adj i j

/-- Every edge of the quotient `blockQuotient b E` comes from exactly one edge of `E`. -/
def HasUniqueReps (E : SimpleGraph V) : Prop :=
  ∀ B B', (blockQuotient b E).Adj B B' →
    ∃! p : V × V, b p.1 = B ∧ b p.2 = B' ∧ E.Adj p.1 p.2

variable {b}

theorem sameBlockGraph_adj {i j : V} : (sameBlockGraph b).Adj i j ↔ i ≠ j ∧ b i = b j := by
  rw [sameBlockGraph, fromRel_adj]
  exact and_congr_right fun _ => or_iff_left_of_imp Eq.symm

theorem crossBlockGraph_adj {i j : V} : (crossBlockGraph b).Adj i j ↔ b i ≠ b j := by
  rw [crossBlockGraph, fromRel_adj]
  refine ⟨fun h => h.2.elim id fun h' => Ne.symm h', fun h => ⟨fun hij => h (hij ▸ rfl), ?_⟩⟩
  exact Or.inl h

theorem blockQuotient_adj {E : SimpleGraph V} {B B' : β} :
    (blockQuotient b E).Adj B B' ↔ B ≠ B' ∧ ∃ i j, b i = B ∧ b j = B' ∧ E.Adj i j := by
  rw [blockQuotient, fromRel_adj]
  refine and_congr_right fun _ => ⟨fun h => h.elim id ?_, Or.inl⟩
  rintro ⟨i, j, hi, hj, hij⟩
  exact ⟨j, i, hj, hi, hij.symm⟩

theorem blockQuotient_adj_of_adj {E : SimpleGraph V} {i j : V} (hij : E.Adj i j)
    (hb : b i ≠ b j) : (blockQuotient b E).Adj (b i) (b j) :=
  blockQuotient_adj.mpr ⟨hb, i, j, rfl, rfl, hij⟩

theorem blockQuotient_mono {E E' : SimpleGraph V} (h : E ≤ E') :
    blockQuotient b E ≤ blockQuotient b E' := fun B B' hBB' => by
  obtain ⟨hne, i, j, hi, hj, hij⟩ := blockQuotient_adj.mp hBB'
  exact blockQuotient_adj.mpr ⟨hne, i, j, hi, hj, h hij⟩

@[simp]
theorem blockQuotient_bot : blockQuotient b (⊥ : SimpleGraph V) = ⊥ := by
  ext B B'
  simp [blockQuotient_adj]

theorem sameBlockGraph_disjoint_crossBlockGraph :
    Disjoint (sameBlockGraph b) (crossBlockGraph b) := by
  rw [disjoint_iff_inf_le]
  intro i j h
  rw [inf_adj, sameBlockGraph_adj, crossBlockGraph_adj] at h
  exact absurd h.1.2 h.2

theorem not_sameBlockGraph_adj_of_le {E : SimpleGraph V} (hE : E ≤ crossBlockGraph b)
    {i j : V} (hij : E.Adj i j) : ¬ (sameBlockGraph b).Adj i j := fun h =>
  crossBlockGraph_adj.mp (hE hij) (sameBlockGraph_adj.mp h).2

/-- Reachability in the same-block graph is equality of blocks. -/
theorem reachable_sameBlockGraph_iff {i j : V} :
    (sameBlockGraph b).Reachable i j ↔ b i = b j := by
  constructor
  · intro h
    have := reachable_comp_of_forall_adj (G' := (⊥ : SimpleGraph β)) b
      (fun u v huv => by rw [(sameBlockGraph_adj.mp huv).2]) h
    exact reachable_bot.mp this
  · intro h
    by_cases hij : i = j
    · exact hij ▸ Reachable.refl _
    · exact (sameBlockGraph_adj.mpr ⟨hij, h⟩).reachable

theorem reachable_sup_sameBlockGraph_of_eq {E : SimpleGraph V} {i j : V} (h : b i = b j) :
    (E ⊔ sameBlockGraph b).Reachable i j :=
  (reachable_sameBlockGraph_iff.mpr h).mono le_sup_right

/-- Projection: a walk in `E ∪ (same-block edges)` projects to a walk of blocks in the
quotient. -/
theorem reachable_blockQuotient_of_reachable {E : SimpleGraph V} {i j : V}
    (h : (E ⊔ sameBlockGraph b).Reachable i j) :
    (blockQuotient b E).Reachable (b i) (b j) := by
  refine reachable_comp_of_forall_adj b (fun u v huv => ?_) h
  by_cases hb : b u = b v
  · rw [hb]
  · rcases huv with huv | huv
    · exact (blockQuotient_adj_of_adj huv hb).reachable
    · exact absurd (sameBlockGraph_adj.mp huv).2 hb

/-- Lifting: a walk of blocks in the quotient lifts to a walk in `E ∪ (same-block edges)`
between any two vertices of the end blocks. -/
theorem reachable_of_reachable_blockQuotient {E : SimpleGraph V} {B B' : β}
    (h : (blockQuotient b E).Reachable B B') {i j : V} (hi : b i = B) (hj : b j = B') :
    (E ⊔ sameBlockGraph b).Reachable i j := by
  obtain ⟨p⟩ := h
  induction p generalizing i with
  | nil => exact reachable_sup_sameBlockGraph_of_eq (hi.trans hj.symm)
  | cons hadj _ ih =>
    obtain ⟨-, a, c, ha, hc, hac⟩ := blockQuotient_adj.mp hadj
    exact (reachable_sup_sameBlockGraph_of_eq (hi.trans ha.symm)).trans
      ((Adj.reachable (Or.inl hac : (E ⊔ sameBlockGraph b).Adj a c)).trans (ih hc hj))

theorem reachable_sup_sameBlockGraph_iff {E : SimpleGraph V} {i j : V} :
    (E ⊔ sameBlockGraph b).Reachable i j ↔ (blockQuotient b E).Reachable (b i) (b j) :=
  ⟨reachable_blockQuotient_of_reachable, fun h => reachable_of_reachable_blockQuotient h rfl rfl⟩

/-- For surjective `b`, `E ∪ (same-block edges)` is connected iff the quotient is. -/
theorem connected_sup_sameBlockGraph_iff (hb : Function.Surjective b) {E : SimpleGraph V} :
    (E ⊔ sameBlockGraph b).Connected ↔ (blockQuotient b E).Connected := by
  constructor
  · intro h
    have : Nonempty V := h.nonempty
    have : Nonempty β := ⟨b (Classical.arbitrary V)⟩
    refine ⟨fun B B' => ?_⟩
    obtain ⟨i, rfl⟩ := hb B
    obtain ⟨j, rfl⟩ := hb B'
    exact reachable_blockQuotient_of_reachable (h.preconnected i j)
  · intro h
    have : Nonempty β := h.nonempty
    have : Nonempty V := ⟨(hb (Classical.arbitrary β)).choose⟩
    exact ⟨fun i j => reachable_sup_sameBlockGraph_iff.mpr (h.preconnected _ _)⟩

/-- Relative forests: for `E` inside the cross-block graph, every edge `uv` of `E` has its
endpoints in distinct components of `(same-block edges) ∪ (E ∖ {uv})` iff the quotient is
acyclic and each of its edges has exactly one representative in `E`. -/
theorem isRelForest_iff {E : SimpleGraph V} (hE : E ≤ crossBlockGraph b) :
    IsRelForest (sameBlockGraph b) E ↔ (blockQuotient b E).IsAcyclic ∧ HasUniqueReps b E := by
  constructor
  · intro hF
    refine ⟨isAcyclic_iff_forall_adj_isBridge.mpr fun B B' hBB' hr => ?_, ?_⟩
    · obtain ⟨-, i, j, rfl, rfl, hij⟩ := blockQuotient_adj.mp hBB'
      have hle : (blockQuotient b E).deleteEdges {s(b i, b j)} ≤
          blockQuotient b (E.deleteEdges {e | e.map b = s(b i, b j)}) := by
        intro C C' h
        rw [deleteEdges_adj] at h
        obtain ⟨h, hne⟩ := h
        obtain ⟨hCC', a, c, rfl, rfl, hac⟩ := blockQuotient_adj.mp h
        refine blockQuotient_adj.mpr ⟨hCC', a, c, rfl, rfl, ?_⟩
        rw [deleteEdges_adj]
        exact ⟨hac, by simpa using hne⟩
      have h2 := reachable_of_reachable_blockQuotient (hr.mono hle) (i := i) (j := j) rfl rfl
      refine hF i j hij (h2.mono (sup_le (le_sup_of_le_right ?_) le_sup_left))
      intro x y hxy
      rw [deleteEdges_adj] at hxy ⊢
      refine ⟨hxy.1, fun hmem => hxy.2 ?_⟩
      rw [Set.mem_singleton_iff] at hmem
      simp [hmem]
    · intro B B' hBB'
      obtain ⟨hne, i, j, rfl, rfl, hij⟩ := blockQuotient_adj.mp hBB'
      refine ⟨(i, j), ⟨rfl, rfl, hij⟩, ?_⟩
      rintro ⟨k, l⟩ ⟨hk, hl, hkl⟩
      by_contra hne'
      have hedge : s(k, l) ≠ s(i, j) := by
        intro heq
        rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hne' rfl
        · exact hne hk.symm
      refine hF i j hij ?_
      have hkl' : (sameBlockGraph b ⊔ E.deleteEdges {s(i, j)}).Adj k l :=
        Or.inr (deleteEdges_adj.mpr ⟨hkl, hedge⟩)
      refine ((reachable_sameBlockGraph_iff.mpr hk.symm).mono le_sup_left).trans
        (hkl'.reachable.trans ((reachable_sameBlockGraph_iff.mpr hl).mono le_sup_left))
  · rintro ⟨hacyc, huniq⟩ u v huv hr
    have hQ : (blockQuotient b E).Adj (b u) (b v) :=
      blockQuotient_adj_of_adj huv (crossBlockGraph_adj.mp (hE huv))
    have hr' : (blockQuotient b (E.deleteEdges {s(u, v)})).Reachable (b u) (b v) :=
      reachable_blockQuotient_of_reachable (by rwa [sup_comm] at hr)
    have hle : blockQuotient b (E.deleteEdges {s(u, v)}) ≤
        (blockQuotient b E).deleteEdges {s(b u, b v)} := by
      intro C C' h
      obtain ⟨hCC', a, c, rfl, rfl, hac⟩ := blockQuotient_adj.mp h
      rw [deleteEdges_adj] at hac
      rw [deleteEdges_adj]
      refine ⟨blockQuotient_adj_of_adj hac.1 hCC', fun heq => hac.2 ?_⟩
      rw [Set.mem_singleton_iff] at heq ⊢
      rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := (huniq _ _ hQ).unique (y₁ := (a, c)) (y₂ := (u, v)) ⟨h1, h2, hac.1⟩
          ⟨rfl, rfl, huv⟩
        simp only [Prod.mk.injEq] at this
        rw [this.1, this.2]
      · have := (huniq _ _ hQ).unique (y₁ := (c, a)) (y₂ := (u, v)) ⟨h2, h1, hac.1.symm⟩
          ⟨rfl, rfl, huv⟩
        simp only [Prod.mk.injEq] at this
        rw [this.1, this.2, Sym2.eq_swap]
    exact isAcyclic_iff_forall_adj_isBridge.mp hacyc hQ (hr'.mono hle)

/-- The edges of `E` correspond to the edges of its quotient when each quotient edge has one
representative. -/
theorem natCard_edgeSet_eq_of_hasUniqueReps {E : SimpleGraph V} (hE : E ≤ crossBlockGraph b)
    (hu : HasUniqueReps b E) : Nat.card E.edgeSet = Nat.card (blockQuotient b E).edgeSet := by
  refine Nat.card_congr (Equiv.ofBijective (fun e => ⟨e.1.map b, ?_⟩) ⟨?_, ?_⟩)
  · obtain ⟨e, he⟩ := e
    induction e using Sym2.ind with
    | h i j =>
      rw [mem_edgeSet] at he
      simpa using blockQuotient_adj_of_adj he (crossBlockGraph_adj.mp (hE he))
  · rintro ⟨e, he⟩ ⟨e', he'⟩ heq
    simp only [Subtype.mk.injEq] at heq ⊢
    induction e using Sym2.ind with
    | h i j =>
    induction e' using Sym2.ind with
    | h k l =>
      rw [mem_edgeSet] at he he'
      have hQ := blockQuotient_adj_of_adj he (crossBlockGraph_adj.mp (hE he))
      simp only [Sym2.map_mk] at heq
      rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := (hu _ _ hQ).unique (y₁ := (i, j)) (y₂ := (k, l)) ⟨rfl, rfl, he⟩
          ⟨h1.symm, h2.symm, he'⟩
        simp only [Prod.mk.injEq] at this
        rw [this.1, this.2]
      · have := (hu _ _ hQ).unique (y₁ := (i, j)) (y₂ := (l, k)) ⟨rfl, rfl, he⟩
          ⟨h1.symm, h2.symm, he'.symm⟩
        simp only [Prod.mk.injEq] at this
        rw [this.1, this.2, Sym2.eq_swap]
  · rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | h B B' =>
      rw [mem_edgeSet] at he
      obtain ⟨-, i, j, rfl, rfl, hij⟩ := blockQuotient_adj.mp he
      exact ⟨⟨s(i, j), hij⟩, by simp⟩

/-- Conversely, if `E` has no more edges than its quotient, each quotient edge has exactly one
representative. -/
theorem hasUniqueReps_of_natCard_le [Finite V] {E : SimpleGraph V} (hE : E ≤ crossBlockGraph b)
    (hc : Nat.card E.edgeSet ≤ Nat.card (blockQuotient b E).edgeSet) : HasUniqueReps b E := by
  let f : E.edgeSet → (blockQuotient b E).edgeSet := fun e => ⟨e.1.map b, by
    obtain ⟨e, he⟩ := e
    induction e using Sym2.ind with
    | h i j =>
      rw [mem_edgeSet] at he
      simpa using blockQuotient_adj_of_adj he (crossBlockGraph_adj.mp (hE he))⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | h B B' =>
      rw [mem_edgeSet] at he
      obtain ⟨-, i, j, rfl, rfl, hij⟩ := blockQuotient_adj.mp he
      exact ⟨⟨s(i, j), hij⟩, by simp [f]⟩
  have hinj := (hsurj.bijective_of_nat_card_le hc).1
  intro B B' hBB'
  obtain ⟨hne, i, j, rfl, rfl, hij⟩ := blockQuotient_adj.mp hBB'
  refine ⟨(i, j), ⟨rfl, rfl, hij⟩, ?_⟩
  rintro ⟨k, l⟩ ⟨hk, hl, hkl⟩
  have heq : f ⟨s(k, l), hkl⟩ = f ⟨s(i, j), hij⟩ := by
    simp only [f, Subtype.mk.injEq, Sym2.map_mk]
    rw [hk, hl]
  have := congrArg Subtype.val (hinj heq)
  simp only at this
  rcases Sym2.eq_iff.mp this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd hk.symm hne

end Block

section Subpartition

variable (X : Finset (Finset ℕ))

/-- `ℰ^intra(X)` (equation (4.7)): the edges `ij`, `i ≠ j`, inside a block
of `X`, as a simple graph on `V_X`. -/
def intraEdges : SimpleGraph (X.biUnion id) :=
  SimpleGraph.fromRel fun i j => ∃ S ∈ X, (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S

/-- `ℰ^inter(X)` (equation (4.6)): the edges `ij` with `i ∈ S`, `j ∈ S'` for
two distinct blocks `S ≠ S'` of `X`, as a simple graph on `V_X`. -/
def interEdges : SimpleGraph (X.biUnion id) :=
  SimpleGraph.fromRel fun i j => ∃ S ∈ X, ∃ S' ∈ X, S ≠ S' ∧ (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S'

/-- The quotient graph `(V_X, E)/X` (Definition 4.10(1)): its vertices are the
blocks of `X`, and `SS'` is an edge if some `i ∈ S`, `j ∈ S'` have `ij ∈ E`. For
`E ⊆ ℰ^inter(X)` the two blocks are automatically distinct. -/
def quotientGraph (E : SimpleGraph (X.biUnion id)) : SimpleGraph X :=
  SimpleGraph.fromRel fun S S' : X => ∃ i j : X.biUnion id,
    (i : ℕ) ∈ (S : Finset ℕ) ∧ (j : ℕ) ∈ (S' : Finset ℕ) ∧ E.Adj i j

/-- `E ∈ 𝖤^X` (Definition 4.10(4); Definition 2.13): `E ⊆ ℰ^inter(X)`
has at least one edge and `(V_X, E ∪ ℰ^intra(X))` is connected. -/
def IsRelConnected (E : SimpleGraph (X.biUnion id)) : Prop :=
  E ≤ interEdges X ∧ E.edgeSet.Nonempty ∧ (E ⊔ intraEdges X).Connected

/-- `E ∈ 𝖳^X`, a tree relative to `X` (Definition 4.10(5)): `E ∈ 𝖤^X`, the
quotient `(V_X, E)/X` is a tree, and each of its edges `SS'` comes from a unique pair `i ∈ S`,
`j ∈ S'` with `ij ∈ E`. -/
def IsRelTree (E : SimpleGraph (X.biUnion id)) : Prop :=
  IsRelConnected X E ∧ (quotientGraph X E).IsTree ∧
    ∀ S S' : X, (quotientGraph X E).Adj S S' →
      ∃! p : X.biUnion id × X.biUnion id,
        (p.1 : ℕ) ∈ (S : Finset ℕ) ∧ (p.2 : ℕ) ∈ (S' : Finset ℕ) ∧ E.Adj p.1 p.2

/-- `E ∈ 𝖤_0^X` (Definition 4.10(6)): `𝖤_0^X = 𝖤^X`, except that
`𝖤_0^{{S}} = {∅}`. -/
def IsRelConnected₀ (E : SimpleGraph (X.biUnion id)) : Prop :=
  IsRelConnected X E ∨ (X.card = 1 ∧ E = ⊥)

/-- `E ∈ 𝖳_0^X` (Definition 4.10(6)): `𝖳_0^X = 𝖳^X`, except that
`𝖳_0^{{S}} = {∅}`. -/
def IsRelTree₀ (E : SimpleGraph (X.biUnion id)) : Prop :=
  IsRelTree X E ∨ (X.card = 1 ∧ E = ⊥)

/-- `(V_X, E)` has a cycle relative to `X` (Definition 4.50): the augmented
graph `(V_X, E ∪ ℰ^intra(X))` has a cycle that is not included in a single block of `X`. -/
def HasRelCycle (E : SimpleGraph (X.biUnion id)) : Prop :=
  ∃ (u : X.biUnion id) (c : (E ⊔ intraEdges X).Walk u u), c.IsCycle ∧
    ¬ ∃ S ∈ X, ∀ v ∈ c.support, (v : ℕ) ∈ S

open scoped Classical in
/-- The finite set `𝖤^X`, written exactly as the edge-set filter of the frozen
`MultipoleBKT.multipoleActivity` (`MultipoleBKT.multipoleActivity_eq`). -/
noncomputable def relConnected : Finset (SimpleGraph (X.biUnion id)) :=
  (Finset.univ : Finset (SimpleGraph (X.biUnion id))).filter (fun E =>
      (∀ i j : X.biUnion id, E.Adj i j →
          ∃ S ∈ X, ∃ S' ∈ X, S ≠ S' ∧ (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S') ∧
        E.edgeSet.Nonempty ∧
        (E ⊔ SimpleGraph.fromRel fun i j : X.biUnion id =>
          ∃ S ∈ X, (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S).Connected)

open scoped Classical in
/-- The finite set `𝖤_0^X`. -/
noncomputable def relConnected₀ : Finset (SimpleGraph (X.biUnion id)) :=
  (Finset.univ : Finset (SimpleGraph (X.biUnion id))).filter (IsRelConnected₀ X)

open scoped Classical in
/-- The finite set `𝖳^X`. -/
noncomputable def relTrees : Finset (SimpleGraph (X.biUnion id)) :=
  (Finset.univ : Finset (SimpleGraph (X.biUnion id))).filter (IsRelTree X)

open scoped Classical in
/-- The finite set `𝖳_0^X`. -/
noncomputable def relTrees₀ : Finset (SimpleGraph (X.biUnion id)) :=
  (Finset.univ : Finset (SimpleGraph (X.biUnion id))).filter (IsRelTree₀ X)

variable {X}

theorem le_interEdges_iff {E : SimpleGraph (X.biUnion id)} :
    E ≤ interEdges X ↔ ∀ i j : X.biUnion id, E.Adj i j →
      ∃ S ∈ X, ∃ S' ∈ X, S ≠ S' ∧ (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S' := by
  constructor
  · intro h i j hij
    obtain ⟨-, h'⟩ := (fromRel_adj _ _ _).mp (h hij)
    rcases h' with h' | ⟨S, hS, S', hS', hne, hi, hj⟩
    · exact h'
    · exact ⟨S', hS', S, hS, hne.symm, hj, hi⟩
  · intro h i j hij
    exact (fromRel_adj _ _ _).mpr ⟨hij.ne, Or.inl (h i j hij)⟩

theorem mem_relConnected {E : SimpleGraph (X.biUnion id)} :
    E ∈ relConnected X ↔ IsRelConnected X E := by
  simp only [relConnected, mem_filter, mem_univ, true_and, IsRelConnected, le_interEdges_iff,
    intraEdges]

theorem mem_relConnected₀ {E : SimpleGraph (X.biUnion id)} :
    E ∈ relConnected₀ X ↔ IsRelConnected₀ X E := by
  simp [relConnected₀]

theorem mem_relTrees {E : SimpleGraph (X.biUnion id)} : E ∈ relTrees X ↔ IsRelTree X E := by
  simp [relTrees]

theorem mem_relTrees₀ {E : SimpleGraph (X.biUnion id)} :
    E ∈ relTrees₀ X ↔ IsRelTree₀ X E := by
  simp [relTrees₀]

open scoped Classical in
/-- The frozen multipole activity is the sum over `E ∈ 𝖤^X` (`MultipoleBKT.relConnected`). -/
theorem multipoleActivity_eq (χ : ℂ → ℝ) (N : ℕ) (β lam M : ℝ) :
    multipoleActivity χ N β lam M X = ∑ E ∈ relConnected X,
      ∫ c : X.biUnion id → ℂ × ℂ,
        ∏ i : X.biUnion id, ∏ j : X.biUnion id,
          if i < j ∧ E.Adj i j then
            (if MultipoleLinked M lam (c i) (c j) then 0 else
                Real.exp (-β * dipoleInteraction χ lam (c i) (c j))) - 1
          else 1
        ∂hierarchicalModel χ N β lam M X :=
  rfl

theorem IsRelConnected.le_interEdges {E : SimpleGraph (X.biUnion id)} (h : IsRelConnected X E) :
    E ≤ interEdges X := h.1

theorem IsRelTree.isRelConnected {E : SimpleGraph (X.biUnion id)} (h : IsRelTree X E) :
    IsRelConnected X E := h.1

theorem interEdges_eq_bot_of_card_eq_one (h : X.card = 1) : interEdges X = ⊥ := by
  obtain ⟨S₀, rfl⟩ := Finset.card_eq_one.mp h
  ext i j
  simp only [interEdges, fromRel_adj, mem_singleton, bot_adj, iff_false, not_and, not_or]
  intro _
  constructor <;> rintro ⟨S, rfl, S', rfl, hne, -⟩ <;> exact hne rfl

theorem IsRelConnected₀.le_interEdges {E : SimpleGraph (X.biUnion id)}
    (h : IsRelConnected₀ X E) : E ≤ interEdges X := by
  rcases h with h | ⟨-, rfl⟩
  · exact h.1
  · exact bot_le

theorem IsRelTree₀.isRelConnected₀ {E : SimpleGraph (X.biUnion id)} (h : IsRelTree₀ X E) :
    IsRelConnected₀ X E := h.imp IsRelTree.isRelConnected id

theorem IsRelTree₀.le_interEdges {E : SimpleGraph (X.biUnion id)} (h : IsRelTree₀ X E) :
    E ≤ interEdges X :=
  h.isRelConnected₀.le_interEdges

theorem relTrees₀_subset_relConnected₀ : relTrees₀ X ⊆ relConnected₀ X := fun _ hT =>
  mem_relConnected₀.mpr (mem_relTrees₀.mp hT).isRelConnected₀

/-! ### Blocks of a subpartition -/

theorem existsUnique_mem_of_isSubpartition (hX : IsSubpartition X) (i : X.biUnion id) :
    ∃! S, S ∈ X ∧ (i : ℕ) ∈ S := by
  obtain ⟨S, hS, hiS⟩ := mem_biUnion.mp i.2
  refine ⟨S, ⟨hS, hiS⟩, fun S' ⟨hS', hiS'⟩ => ?_⟩
  by_contra hne
  exact Finset.disjoint_left.mp (hX.2 (mem_coe.mpr hS') (mem_coe.mpr hS) hne) hiS' hiS

/-- The block `[i]^X` of `X` containing `i ∈ V_X` (Definition 4.9(3)). -/
def blockOf (hX : IsSubpartition X) (i : X.biUnion id) : X :=
  ⟨X.choose (fun S => (i : ℕ) ∈ S) (existsUnique_mem_of_isSubpartition hX i),
    (X.choose_spec _ _).1⟩

theorem mem_blockOf (hX : IsSubpartition X) (i : X.biUnion id) :
    (i : ℕ) ∈ ((blockOf hX i : X) : Finset ℕ) :=
  (X.choose_spec _ (existsUnique_mem_of_isSubpartition hX i)).2

theorem blockOf_eq_iff (hX : IsSubpartition X) {i : X.biUnion id} {S : X} :
    blockOf hX i = S ↔ (i : ℕ) ∈ (S : Finset ℕ) := by
  refine ⟨fun h => h ▸ mem_blockOf hX i, fun h => Subtype.ext ?_⟩
  exact (existsUnique_mem_of_isSubpartition hX i).unique ⟨(blockOf hX i).2, mem_blockOf hX i⟩
    ⟨S.2, h⟩

theorem blockOf_surjective (hX : IsSubpartition X) : Function.Surjective (blockOf hX) := by
  intro S
  obtain ⟨i, hi⟩ := hX.1 S S.2
  exact ⟨⟨i, mem_biUnion.mpr ⟨S, S.2, hi⟩⟩, (blockOf_eq_iff hX).mpr hi⟩

theorem exists_mem_mem_iff (hX : IsSubpartition X) {i j : X.biUnion id} :
    (∃ S ∈ X, (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S) ↔ blockOf hX i = blockOf hX j := by
  constructor
  · rintro ⟨S, hS, hi, hj⟩
    rw [(blockOf_eq_iff hX (S := ⟨S, hS⟩)).mpr hi, (blockOf_eq_iff hX (S := ⟨S, hS⟩)).mpr hj]
  · intro h
    refine ⟨_, (blockOf hX i).2, mem_blockOf hX i, ?_⟩
    rw [h]
    exact mem_blockOf hX j

theorem exists_ne_mem_mem_iff (hX : IsSubpartition X) {i j : X.biUnion id} :
    (∃ S ∈ X, ∃ S' ∈ X, S ≠ S' ∧ (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S') ↔
      blockOf hX i ≠ blockOf hX j := by
  constructor
  · rintro ⟨S, hS, S', hS', hne, hi, hj⟩ h
    rw [(blockOf_eq_iff hX (S := ⟨S, hS⟩)).mpr hi, (blockOf_eq_iff hX (S := ⟨S', hS'⟩)).mpr hj]
      at h
    exact hne (congrArg Subtype.val h)
  · intro h
    exact ⟨_, (blockOf hX i).2, _, (blockOf hX j).2, fun h' => h (Subtype.ext h'),
      mem_blockOf hX i, mem_blockOf hX j⟩

theorem intraEdges_eq (hX : IsSubpartition X) :
    intraEdges X = sameBlockGraph (blockOf hX) := by
  ext i j
  simp only [intraEdges, sameBlockGraph, fromRel_adj, exists_mem_mem_iff hX]

theorem interEdges_eq (hX : IsSubpartition X) :
    interEdges X = crossBlockGraph (blockOf hX) := by
  ext i j
  simp only [interEdges, crossBlockGraph, fromRel_adj, exists_ne_mem_mem_iff hX]

theorem quotientGraph_eq (hX : IsSubpartition X) (E : SimpleGraph (X.biUnion id)) :
    quotientGraph X E = blockQuotient (blockOf hX) E := by
  ext S S'
  simp only [quotientGraph, blockQuotient, fromRel_adj, blockOf_eq_iff hX]

theorem intraEdges_adj (hX : IsSubpartition X) {i j : X.biUnion id} :
    (intraEdges X).Adj i j ↔ i ≠ j ∧ blockOf hX i = blockOf hX j := by
  rw [intraEdges_eq hX, sameBlockGraph_adj]

theorem interEdges_adj (hX : IsSubpartition X) {i j : X.biUnion id} :
    (interEdges X).Adj i j ↔ blockOf hX i ≠ blockOf hX j := by
  rw [interEdges_eq hX, crossBlockGraph_adj]

theorem reachable_intraEdges_iff (hX : IsSubpartition X) {i j : X.biUnion id} :
    (intraEdges X).Reachable i j ↔ blockOf hX i = blockOf hX j := by
  rw [intraEdges_eq hX, reachable_sameBlockGraph_iff]

theorem disjoint_interEdges_intraEdges (hX : IsSubpartition X) :
    Disjoint (interEdges X) (intraEdges X) := by
  rw [intraEdges_eq hX, interEdges_eq hX]
  exact sameBlockGraph_disjoint_crossBlockGraph.symm

theorem not_intraEdges_adj_of_le (hX : IsSubpartition X) {E : SimpleGraph (X.biUnion id)}
    (hE : E ≤ interEdges X) {i j : X.biUnion id} (hij : E.Adj i j) :
    ¬ (intraEdges X).Adj i j := by
  rw [intraEdges_eq hX]
  rw [interEdges_eq hX] at hE
  exact not_sameBlockGraph_adj_of_le hE hij

/-! ### Connectedness relative to `X` -/

/-- Reachability in `E ∪ ℰ^intra(X)` is reachability of the blocks in the quotient graph. -/
theorem reachable_sup_intraEdges_iff (hX : IsSubpartition X) {E : SimpleGraph (X.biUnion id)}
    {i j : X.biUnion id} :
    (E ⊔ intraEdges X).Reachable i j ↔
      (quotientGraph X E).Reachable (blockOf hX i) (blockOf hX j) := by
  rw [intraEdges_eq hX, quotientGraph_eq hX, reachable_sup_sameBlockGraph_iff]

theorem connected_sup_intraEdges_iff (hX : IsSubpartition X) {E : SimpleGraph (X.biUnion id)} :
    (E ⊔ intraEdges X).Connected ↔ (quotientGraph X E).Connected := by
  rw [intraEdges_eq hX, quotientGraph_eq hX,
    connected_sup_sameBlockGraph_iff (blockOf_surjective hX)]

theorem connected_sup_intraEdges_of_card_eq_one (hX : IsSubpartition X) (h : X.card = 1)
    (E : SimpleGraph (X.biUnion id)) : (E ⊔ intraEdges X).Connected := by
  rw [connected_sup_intraEdges_iff hX]
  have hc : Fintype.card X = 1 := by rw [Fintype.card_coe, h]
  obtain ⟨S₀, hS₀⟩ := Fintype.card_eq_one_iff.mp hc
  have : Nonempty X := ⟨S₀⟩
  exact ⟨fun S S' => by rw [hS₀ S, hS₀ S']⟩

theorem card_eq_one_of_connected_intraEdges (hX : IsSubpartition X)
    (h : (intraEdges X).Connected) : X.card = 1 := by
  rw [← bot_sup_eq (intraEdges X), connected_sup_intraEdges_iff hX, quotientGraph_eq hX,
    blockQuotient_bot] at h
  have : Nonempty X := h.nonempty
  rw [← Fintype.card_coe]
  exact Fintype.card_eq_one_iff.mpr ⟨Classical.arbitrary X, fun S =>
    reachable_bot.mp (h.preconnected S _)⟩

/-- `E ∈ 𝖤_0^X` iff `E ⊆ ℰ^inter(X)` and `(V_X, E ∪ ℰ^intra(X))` is connected. -/
theorem isRelConnected₀_iff (hX : IsSubpartition X) {E : SimpleGraph (X.biUnion id)} :
    IsRelConnected₀ X E ↔ E ≤ interEdges X ∧ (E ⊔ intraEdges X).Connected := by
  constructor
  · rintro (⟨h1, -, h3⟩ | ⟨h1, rfl⟩)
    · exact ⟨h1, h3⟩
    · exact ⟨bot_le, connected_sup_intraEdges_of_card_eq_one hX h1 ⊥⟩
  · rintro ⟨hle, hconn⟩
    by_cases h1 : X.card = 1
    · exact Or.inr ⟨h1, le_bot_iff.mp (hle.trans (interEdges_eq_bot_of_card_eq_one h1).le)⟩
    · refine Or.inl ⟨hle, ?_, hconn⟩
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty, edgeSet_eq_empty] at hempty
      rw [hempty, bot_sup_eq] at hconn
      exact h1 (card_eq_one_of_connected_intraEdges hX hconn)

/-- `E ∈ 𝖤_0^X` iff `E ⊆ ℰ^inter(X)` and the quotient graph `(V_X, E)/X` is connected. -/
theorem isRelConnected₀_iff_quotient (hX : IsSubpartition X) {E : SimpleGraph (X.biUnion id)} :
    IsRelConnected₀ X E ↔ E ≤ interEdges X ∧ (quotientGraph X E).Connected := by
  rw [isRelConnected₀_iff hX, connected_sup_intraEdges_iff hX]

/-- `𝖤^X` is `𝖤_0^X` away from the single-block case, where it is empty. -/
theorem isRelConnected_iff {E : SimpleGraph (X.biUnion id)} :
    IsRelConnected X E ↔ IsRelConnected₀ X E ∧ X.card ≠ 1 := by
  constructor
  · intro h
    refine ⟨Or.inl h, fun h1 => ?_⟩
    obtain ⟨e, he⟩ := h.2.1
    rw [le_bot_iff.mp (h.1.trans (interEdges_eq_bot_of_card_eq_one h1).le)] at he
    simp at he
  · rintro ⟨h | ⟨h1, -⟩, hne⟩
    · exact h
    · exact absurd h1 hne

/-! ### Trees relative to `X` -/

/-- For `E ⊆ ℰ^inter(X)`, `E` is a forest relative to `ℰ^intra(X)` iff the quotient graph is
acyclic and each of its edges `SS'` comes from a unique pair `i ∈ S`, `j ∈ S'`, `ij ∈ E`. -/
theorem isRelForest_intraEdges_iff (hX : IsSubpartition X) {E : SimpleGraph (X.biUnion id)}
    (hE : E ≤ interEdges X) :
    IsRelForest (intraEdges X) E ↔ (quotientGraph X E).IsAcyclic ∧
      ∀ S S' : X, (quotientGraph X E).Adj S S' →
        ∃! p : X.biUnion id × X.biUnion id,
          (p.1 : ℕ) ∈ (S : Finset ℕ) ∧ (p.2 : ℕ) ∈ (S' : Finset ℕ) ∧ E.Adj p.1 p.2 := by
  rw [interEdges_eq hX] at hE
  rw [intraEdges_eq hX, quotientGraph_eq hX, isRelForest_iff hE, HasUniqueReps]
  simp only [blockOf_eq_iff hX]

/-- `E ∈ 𝖳_0^X` iff `E ⊆ ℰ^inter(X)`, `(V_X, E ∪ ℰ^intra(X))` is connected, and no edge `ij`
of `E` has its endpoints joined in `ℰ^intra(X) ∪ (E ∖ {ij})`. -/
theorem isRelTree₀_iff (hX : IsSubpartition X) {E : SimpleGraph (X.biUnion id)} :
    IsRelTree₀ X E ↔ E ≤ interEdges X ∧ (E ⊔ intraEdges X).Connected ∧
      IsRelForest (intraEdges X) E := by
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, rfl⟩)
    · exact ⟨h1.1, h1.2.2, (isRelForest_intraEdges_iff hX h1.1).mpr ⟨h2.isAcyclic, h3⟩⟩
    · exact ⟨bot_le, connected_sup_intraEdges_of_card_eq_one hX h1 ⊥, fun _ _ h => h.elim⟩
  · rintro ⟨hle, hconn, hF⟩
    by_cases h1 : X.card = 1
    · exact Or.inr ⟨h1, le_bot_iff.mp (hle.trans (interEdges_eq_bot_of_card_eq_one h1).le)⟩
    · have hrc : IsRelConnected X E :=
        isRelConnected_iff.mpr ⟨(isRelConnected₀_iff hX).mpr ⟨hle, hconn⟩, h1⟩
      obtain ⟨hacyc, huniq⟩ := (isRelForest_intraEdges_iff hX hle).mp hF
      exact Or.inl ⟨hrc, ⟨(connected_sup_intraEdges_iff hX).mp hconn, hacyc⟩, huniq⟩

/-- For `E ⊆ ℰ^inter(X)`, `(V_X, E)` has a cycle relative to `X` iff some edge `ij` of `E` has its
endpoints joined in `ℰ^intra(X) ∪ (E ∖ {ij})`. -/
theorem hasRelCycle_iff_not_isRelForest (hX : IsSubpartition X)
    {E : SimpleGraph (X.biUnion id)} (hE : E ≤ interEdges X) :
    HasRelCycle X E ↔ ¬ IsRelForest (intraEdges X) E := by
  constructor
  · rintro ⟨u, c, hc, hns⟩ hF
    have hexE : ∃ e ∈ c.edges, e ∈ E.edgeSet := by
      by_contra hall
      simp only [not_exists, not_and] at hall
      have hK : ∀ e ∈ c.edges, e ∈ (intraEdges X).edgeSet := fun e he => by
        have := c.edges_subset_edgeSet he
        rw [edgeSet_sup] at this
        exact this.resolve_left (hall e he)
      refine hns ⟨_, (blockOf hX u).2, fun v hv => ?_⟩
      rw [← Walk.support_transfer c hK, Walk.mem_support_iff_exists_append] at hv
      obtain ⟨q, -, -⟩ := hv
      rw [(reachable_intraEdges_iff hX).mp ⟨q⟩]
      exact mem_blockOf hX v
    obtain ⟨e, hec, heE⟩ := hexE
    induction e using Sym2.ind with
    | h x y =>
      have hxy : E.Adj x y := heE
      have hr := ((adj_and_reachable_delete_edges_iff_exists_cycle).mpr ⟨u, c, hc, hec⟩).2
      refine hF x y hxy (hr.mono fun a b hab => ?_)
      rw [deleteEdges_adj, sup_adj] at hab
      rcases hab with ⟨hab | hab, hne⟩
      · exact Or.inr (deleteEdges_adj.mpr ⟨hab, hne⟩)
      · exact Or.inl hab
  · intro hnF
    simp only [IsRelForest, not_forall, not_not] at hnF
    obtain ⟨u, v, huv, hr⟩ := hnF
    have hle : intraEdges X ⊔ E.deleteEdges {s(u, v)} ≤
        (E ⊔ intraEdges X).deleteEdges {s(u, v)} := by
      intro a b hab
      rw [deleteEdges_adj, sup_adj]
      rcases hab with hab | hab
      · refine ⟨Or.inr hab, fun hmem => ?_⟩
        rw [Set.mem_singleton_iff] at hmem
        rcases Sym2.eq_iff.mp hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact not_intraEdges_adj_of_le hX hE huv hab
        · exact not_intraEdges_adj_of_le hX hE huv hab.symm
      · rw [deleteEdges_adj] at hab
        exact ⟨Or.inl hab.1, hab.2⟩
    obtain ⟨w, c, hc, he⟩ := (adj_and_reachable_delete_edges_iff_exists_cycle).mp
      ⟨Or.inl huv, hr.mono hle⟩
    refine ⟨w, c, hc, ?_⟩
    rintro ⟨S, hS, hall⟩
    have hu := hall u (c.fst_mem_support_of_mem_edges he)
    have hv := hall v (c.snd_mem_support_of_mem_edges he)
    have := (interEdges_adj hX).mp (hE huv)
    rw [(blockOf_eq_iff hX (S := ⟨S, hS⟩)).mpr hu, (blockOf_eq_iff hX (S := ⟨S, hS⟩)).mpr hv]
      at this
    exact this rfl

/-- `E ∈ 𝖳_0^X` iff `E ∈ 𝖤_0^X` and `(V_X, E)` has no cycle relative to `X`. -/
theorem isRelTree₀_iff_not_hasRelCycle (hX : IsSubpartition X)
    {E : SimpleGraph (X.biUnion id)} :
    IsRelTree₀ X E ↔ IsRelConnected₀ X E ∧ ¬ HasRelCycle X E := by
  rw [isRelTree₀_iff hX, isRelConnected₀_iff hX]
  constructor
  · rintro ⟨hle, hconn, hF⟩
    exact ⟨⟨hle, hconn⟩, fun h => (hasRelCycle_iff_not_isRelForest hX hle).mp h hF⟩
  · rintro ⟨⟨hle, hconn⟩, hnc⟩
    exact ⟨hle, hconn, not_not.mp fun h => hnc ((hasRelCycle_iff_not_isRelForest hX hle).mpr h)⟩

/-- A relative tree has as many edges as its quotient. -/
theorem IsRelTree₀.natCard_edgeSet_eq (hX : IsSubpartition X) {E : SimpleGraph (X.biUnion id)}
    (h : IsRelTree₀ X E) :
    Nat.card E.edgeSet = Nat.card (quotientGraph X E).edgeSet := by
  obtain ⟨hle, -, hF⟩ := (isRelTree₀_iff hX).mp h
  rw [intraEdges_eq hX] at hF
  rw [interEdges_eq hX] at hle
  rw [quotientGraph_eq hX]
  exact natCard_edgeSet_eq_of_hasUniqueReps hle ((isRelForest_iff hle).mp hF).2

/-- The quotient of a relative tree is a tree on the blocks. -/
theorem IsRelTree₀.isTree_quotientGraph (hX : IsSubpartition X)
    {E : SimpleGraph (X.biUnion id)} (h : IsRelTree₀ X E) : (quotientGraph X E).IsTree := by
  obtain ⟨hle, hconn, hF⟩ := (isRelTree₀_iff hX).mp h
  exact ⟨(connected_sup_intraEdges_iff hX).mp hconn,
    ((isRelForest_intraEdges_iff hX hle).mp hF).1⟩

/-- A relative tree has `|X| - 1` edges. -/
theorem IsRelTree₀.natCard_edgeSet (hX : IsSubpartition X) {E : SimpleGraph (X.biUnion id)}
    (h : IsRelTree₀ X E) : Nat.card E.edgeSet + 1 = X.card := by
  rw [h.natCard_edgeSet_eq hX, (isTree_iff_connected_and_card.mp (h.isTree_quotientGraph hX)).2,
    Nat.card_eq_fintype_card (α := X), Fintype.card_coe]

/-- A relative tree has `|X| - 1` edges (`edgeFinset` form). -/
theorem IsRelTree₀.card_edgeFinset (hX : IsSubpartition X) {E : SimpleGraph (X.biUnion id)}
    [Fintype E.edgeSet] (h : IsRelTree₀ X E) : E.edgeFinset.card + 1 = X.card := by
  rw [edgeFinset_card, ← Nat.card_eq_fintype_card]
  exact h.natCard_edgeSet hX

/-- `E ∈ 𝖳_0^X` iff `E ⊆ ℰ^inter(X)`, the quotient graph `(V_X, E)/X` is a tree on the blocks,
and `E` has `|X| - 1` edges. -/
theorem isRelTree₀_iff_card (hX : IsSubpartition X) {E : SimpleGraph (X.biUnion id)} :
    IsRelTree₀ X E ↔ E ≤ interEdges X ∧ (quotientGraph X E).IsTree ∧
      Nat.card E.edgeSet + 1 = X.card := by
  refine ⟨fun h => ⟨h.le_interEdges, h.isTree_quotientGraph hX, h.natCard_edgeSet hX⟩, ?_⟩
  rintro ⟨hle, htree, hcard⟩
  rw [isRelTree₀_iff hX]
  refine ⟨hle, (connected_sup_intraEdges_iff hX).mpr htree.connected, ?_⟩
  rw [isRelForest_intraEdges_iff hX hle]
  refine ⟨htree.isAcyclic, ?_⟩
  have hQ := (isTree_iff_connected_and_card.mp htree).2
  rw [Nat.card_eq_fintype_card (α := X), Fintype.card_coe, ← hcard,
    Nat.add_right_cancel_iff] at hQ
  have hle' := hle
  rw [interEdges_eq hX] at hle'
  have hu := hasUniqueReps_of_natCard_le hle' (by rw [← quotientGraph_eq hX, hQ])
  intro S S' hSS'
  rw [quotientGraph_eq hX] at hSS'
  simpa only [blockOf_eq_iff hX] using hu S S' hSS'

end Subpartition

/-! ### Further notions of Definitions 4.9–4.10 -/

section Further

variable (X : Finset (Finset ℕ))

open scoped Classical in
/-- `Res(X, E)` (Definition 4.9(5)): the blocks of `X` containing a vertex
incident to an edge of `E`. -/
noncomputable def restrictBlocks (E : SimpleGraph (X.biUnion id)) : Finset (Finset ℕ) :=
  X.filter fun S => ∃ i j : X.biUnion id, (i : ℕ) ∈ S ∧ E.Adj i j

/-- The coarsening `Coarse_X(X_1, …, X_n)` (Definition 4.9(6), equation (4.8)), for the set `G = {X_1, …, X_n}` of groups: each group `X_i` (a nonempty set of
blocks of `X`, the groups being disjoint) is replaced by the single block `V_{X_i}`, and the
blocks of `X` in no group are kept. It depends on the groups only through the set `G`. -/
def coarsen (G : Finset (Finset (Finset ℕ))) : Finset (Finset ℕ) :=
  G.image (fun Y => Y.biUnion id) ∪ X.filter fun S => ∀ Y ∈ G, S ∉ Y

/-- The edge multiplicity `m_E(S, S')` of the multigraph quotient (Definition 4.10(2)): the number of edges `ij ∈ E` with `i ∈ S`, `j ∈ S'`. -/
noncomputable def quotientMult (E : SimpleGraph (X.biUnion id)) (S S' : Finset ℕ) : ℕ :=
  {e | e ∈ E.edgeSet ∧ ∃ i j : X.biUnion id, (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S' ∧ e = s(i, j)}.ncard

open scoped Classical in
/-- The degree `deg_E(S) = ∑_{i ∈ S} deg_{(V_X, E)}(i)` of a block (Definition 4.10(7)). -/
noncomputable def blockDegree (E : SimpleGraph (X.biUnion id)) (S : Finset ℕ) : ℕ :=
  ∑ i ∈ S.subtype (· ∈ X.biUnion id), E.degree i

variable {X}

@[simp]
theorem coarsen_empty : coarsen X ∅ = X := by
  ext S
  simp [coarsen]

/-- Two blocks of a coarsening sharing a point are equal. -/
theorem eq_of_mem_of_mem_coarsen (hX : IsSubpartition X) {G : Finset (Finset (Finset ℕ))}
    (hGX : ∀ Y ∈ G, Y ⊆ X) (hG : (G : Set (Finset (Finset ℕ))).PairwiseDisjoint id)
    {A B : Finset ℕ} (hA : A ∈ coarsen X G) (hB : B ∈ coarsen X G) {x : ℕ} (hxA : x ∈ A)
    (hxB : x ∈ B) : A = B := by
  have hXeq : ∀ S ∈ X, ∀ S' ∈ X, x ∈ S → x ∈ S' → S = S' := fun S hS S' hS' h h' => by
    by_contra hne
    exact Finset.disjoint_left.mp (hX.2 (mem_coe.mpr hS) (mem_coe.mpr hS') hne) h h'
  simp only [coarsen, mem_union, mem_image, mem_filter] at hA hB
  rcases hA with ⟨Y, hY, rfl⟩ | ⟨hSA, hA⟩ <;> rcases hB with ⟨Y', hY', rfl⟩ | ⟨hSB, hB⟩
  · obtain ⟨S, hS, hxS⟩ := mem_biUnion.mp hxA
    obtain ⟨S', hS', hxS'⟩ := mem_biUnion.mp hxB
    have hSS' := hXeq S (hGX Y hY hS) S' (hGX Y' hY' hS') hxS hxS'
    subst hSS'
    by_cases hYY' : Y = Y'
    · rw [hYY']
    · exact absurd hS' (Finset.disjoint_left.mp (hG (mem_coe.mpr hY) (mem_coe.mpr hY') hYY') hS)
  · obtain ⟨S, hS, hxS⟩ := mem_biUnion.mp hxA
    have hSS' := hXeq S (hGX Y hY hS) B hSB hxS hxB
    subst hSS'
    exact absurd hS (hB Y hY)
  · obtain ⟨S', hS', hxS'⟩ := mem_biUnion.mp hxB
    have hSS' := hXeq A hSA S' (hGX Y' hY' hS') hxA hxS'
    subst hSS'
    exact absurd hS' (hA Y' hY')
  · exact hXeq A hSA B hSB hxA hxB

/-- A coarsening of a subpartition along nonempty disjoint groups of blocks is a
subpartition. -/
theorem isSubpartition_coarsen (hX : IsSubpartition X) {G : Finset (Finset (Finset ℕ))}
    (hGX : ∀ Y ∈ G, Y ⊆ X) (hGne : ∀ Y ∈ G, Y.Nonempty)
    (hG : (G : Set (Finset (Finset ℕ))).PairwiseDisjoint id) : IsSubpartition (coarsen X G) := by
  refine ⟨fun A hA => ?_, fun A hA B hB hne => ?_⟩
  · simp only [coarsen, mem_union, mem_image, mem_filter] at hA
    rcases hA with ⟨Y, hY, rfl⟩ | ⟨hS, -⟩
    · obtain ⟨S, hS⟩ := hGne Y hY
      obtain ⟨x, hx⟩ := hX.1 S (hGX Y hY hS)
      exact ⟨x, mem_biUnion.mpr ⟨S, hS, hx⟩⟩
    · exact hX.1 A hS
  · exact Finset.disjoint_left.mpr fun _ hxA hxB =>
      hne (eq_of_mem_of_mem_coarsen hX hGX hG hA hB hxA hxB)

/-- A coarsening has the same set of points: `V_{Coarse_X(X_1, …, X_n)} = V_X`. -/
theorem biUnion_coarsen {G : Finset (Finset (Finset ℕ))} (hGX : ∀ Y ∈ G, Y ⊆ X) :
    (coarsen X G).biUnion id = X.biUnion id := by
  ext x
  simp only [mem_biUnion, coarsen, mem_union, mem_image, mem_filter, id]
  constructor
  · rintro ⟨A, hA | hA, hxA⟩
    · obtain ⟨Y, hY, rfl⟩ := hA
      obtain ⟨S, hS, hxS⟩ := mem_biUnion.mp hxA
      exact ⟨S, hGX Y hY hS, hxS⟩
    · exact ⟨A, hA.1, hxA⟩
  · rintro ⟨S, hS, hxS⟩
    by_cases h : ∃ Y ∈ G, S ∈ Y
    · obtain ⟨Y, hY, hSY⟩ := h
      exact ⟨Y.biUnion id, Or.inl ⟨Y, hY, rfl⟩, mem_biUnion.mpr ⟨S, hSY, hxS⟩⟩
    · push Not at h
      exact ⟨S, Or.inr ⟨hS, h⟩, hxS⟩

end Further

end MultipoleBKT

end
